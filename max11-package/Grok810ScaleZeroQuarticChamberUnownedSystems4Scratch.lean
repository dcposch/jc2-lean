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

/-! # Unowned multi-carrier systems, part 4/15

3 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems4810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDG` / `CG·DD·CCC`: the 5 face rows force `d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCDG18810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr2 : (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr3 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr4 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hDc : (d : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : d * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * c * d) * hr0 + ((18 / 55 : k) * d) * hr1 + ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * hr2
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDG` / `CG·DD·CCC` dies on the 5-carrier system (μ, π, N₂, N₃, N₄). -/
theorem quarticChamberBCDG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG18810 A B C D E F G)
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
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
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
    muQuarticChamberRest6003810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hEz hFz (by omega) (by omega) (by omega) hz0l hz0beta (Or.inr (by omega)) hz0delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
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
    piQuarticChamberRest6004810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hEz hFz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz1l hz1beta (Or.inr (by omega)) hz1delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
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
  have hdp2 : A.natDegree < 2 * C.natDegree + D.natDegree := by
    omega
  have hdz2 : 0 < 2 * C.natDegree + D.natDegree := by omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree) := by
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
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
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
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
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
  have hz2zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree) := by
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
  have hz2theta : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree < 2 * C.natDegree + D.natDegree) := by
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
  have hr2 : (n2QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest6000810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hEz hFz (by omega) (by omega) (by omega) hz2l hz2beta (Or.inr (by omega)) hz2delta (Or.inr (by omega)) hz2zeta (Or.inr (by omega)) hz2theta
  have hct2 := n2QuarticChamberFace6000810_coeff_top hCne hDne hGne (A := A) (B := B) (E := E) (F := F) (by omega)
  have hq2 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    omega
  rw [degreeZeroN2Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree := by
    omega
  have hdz3 : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz3l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 4 * B.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * B.natDegree + D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz3beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz3delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz3zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz3theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hr3 : (n3QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest6000810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hEz hFz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz3l hz3beta (Or.inr (by omega)) hz3delta (Or.inr (by omega)) hz3zeta (Or.inr (by omega)) hz3theta
  have hct3 := n3QuarticChamberFace6000810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by omega)
  have hq3 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    omega
  rw [degreeZeroN3Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : (45 / 2048 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-15 / 256 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hdp4 : A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree := by
    omega
  have hdz4 : 0 < 2 * A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz4l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 6 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + B.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz4beta : beta = 0 ∨ (7 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * B.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz4delta : delta = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz4zeta : zeta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz4theta : theta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hr4 : (n4QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree :=
    n4QuarticChamberRest6000810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hEz hFz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz4l hz4beta (Or.inr (by omega)) hz4delta (Or.inr (by omega)) hz4zeta (Or.inr (by omega)) hz4theta
  have hct4 := n4QuarticChamberFace6000810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by omega)
  have hq4 : (degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN4Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi
    omega
  rw [degreeZeroN4Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hin4 : (-15 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct4.symm.trans hq4
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemBCDG18810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hDc hGc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCFG` / `BF·CF·BBB·BBC·BCC·CCC`: the 6 face rows force `a * b * f ^ 3 = 0`. -/
theorem quarticUnownedSystemBCFG11810_cert
    (a b c d e f g : k)
    (hr0 : (5 / 512 : k) * a * b ^ 3 + (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * c * f = 0)
    (hr1 : (15 / 512 : k) * a * b ^ 2 * c + (-5 / 64 : k) * a * b * f + (-5 / 128 : k) * c ^ 3 = 0)
    (hr2 : (-5 / 4096 : k) * a ^ 2 * b ^ 3 + (15 / 1024 : k) * a * b * c ^ 2 + (-5 / 128 : k) * a * c * f = 0)
    (hr3 : (-5 / 65536 : k) * a ^ 3 * b ^ 3 + (15 / 16384 : k) * a ^ 2 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 2 * c * f = 0)
    (hr4 : (15 / 4096 : k) * a ^ 2 * b ^ 4 + (-45 / 512 : k) * a * b ^ 2 * c ^ 2 + (5 / 32 : k) * a * b * c * f + (-5 / 16 : k) * a * f ^ 2 + (15 / 256 : k) * c ^ 4 = 0)
    (hr5 : (-5 / 65536 : k) * a ^ 4 * b ^ 3 + (15 / 16384 : k) * a ^ 3 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 3 * c * f = 0)
    (hAc : (a : k) ≠ 0)
    (hBc : (b : k) ≠ 0)
    (hFc : (f : k) ≠ 0) :
    False := by
  have ht : a * b * f ^ 3 = 0 := by
    linear_combination ((-1 / 10 : k) * a * b ^ 3 * c + (1 : k) * a * b ^ 2 * f + (-4 / 15 : k) * c ^ 2 * f) * hr0 + ((2 / 5 : k) * b ^ 2 * c ^ 2 + (-16 / 5 : k) * b * c * f + (-32 / 15 : k) * f ^ 2) * hr1 + ((4 / 15 : k) * b ^ 2 * c + (-8 / 3 : k) * b * f) * hr4
  exact (mul_ne_zero (mul_ne_zero hAc hBc) (pow_ne_zero 3 hFc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCFG` / `BF·CF·BBB·BBC·BCC·CCC` dies on the 6-carrier system (κ, μ, ν, ο, π, Π). -/
theorem quarticChamberBCFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG11810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    omega
  have hdz0 : 0 < A.natDegree + 3 * B.natDegree := by omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
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
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
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
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
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
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
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
  have hr0 : (kappaQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6001810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz hEz (by omega) hz0l hz0beta (Or.inr (by omega)) hz0delta hz0zeta (Or.inr (by omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6001810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by omega) (by omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    omega
  rw [degreeZeroKappaQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
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
  have hr1 : (muQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest6001810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz hEz (by omega) (by omega) hz1l hz1beta (Or.inr (by omega)) hz1delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct1 := muQuarticChamberFace6001810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by omega) (by omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    omega
  rw [degreeZeroMuQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 64 : k) * A.leadingCoeff * B.leadingCoeff * F.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 3 * B.natDegree := by
    omega
  have hdz2 : 0 < 2 * A.natDegree + 3 * B.natDegree := by omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2theta : theta = 0 ∨ (2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hr2 : (nuQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree :=
    nuQuarticChamberRest6001810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hDz hEz (by omega) (by omega) (by omega) hz2l hz2beta (Or.inr (by omega)) hz2delta (Or.inr (by omega)) hz2zeta (Or.inr (by omega)) hz2theta
  have hct2 := nuQuarticChamberFace6001810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by omega) (by omega)
  have hq2 : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnu]
    omega
  rw [degreeZeroNuQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (-5 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 + (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * C.leadingCoeff * F.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 3 * A.natDegree + 3 * B.natDegree := by
    omega
  have hdz3 : 0 < 3 * A.natDegree + 3 * B.natDegree := by omega
  have hz3l : l = 0 ∨ (7 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz3beta : beta = 0 ∨ (6 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz3delta : delta = 0 ∨ (5 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz3zeta : zeta = 0 ∨ (4 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz3theta : theta = 0 ∨ (3 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hr3 : (omicronQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * A.natDegree + 3 * B.natDegree :=
    omicronQuarticChamberRest6001810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hDz hEz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz3l hz3beta (Or.inr (by omega)) hz3delta (Or.inr (by omega)) hz3zeta (Or.inr (by omega)) hz3theta
  have hct3 := omicronQuarticChamberFace6001810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by omega) (by omega)
  have hq3 : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [homi]
    omega
  rw [degreeZeroOmicronQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : (-5 / 65536 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hdp4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    omega
  have hdz4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by omega
  have hz4l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz4beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz4delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
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
  have hr4 : (piQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6002810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hDz hEz (by omega) (by omega) (by omega) (by omega) (by omega) hz4l hz4beta (Or.inr (by omega)) hz4delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct4 := piQuarticChamberFace6002810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by omega) (by omega) (by omega) (by omega)
  have hq4 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6002_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hin4 : (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (-45 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (5 / 32 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-5 / 16 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 = 0 :=
    hct4.symm.trans hq4
  have hdp5 : A.natDegree < 4 * A.natDegree + 3 * B.natDegree := by
    omega
  have hdz5 : 0 < 4 * A.natDegree + 3 * B.natDegree := by omega
  have hz5l : l = 0 ∨ (8 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 6 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz5beta : beta = 0 ∨ (7 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz5delta : delta = 0 ∨ (6 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz5zeta : zeta = 0 ∨ (5 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz5theta : theta = 0 ∨ (4 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hr5 : (primitiveQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * A.natDegree + 3 * B.natDegree :=
    primitiveQuarticChamberRest6001810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz5 hDz hEz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz5l hz5beta (Or.inr (by omega)) hz5delta (Or.inr (by omega)) hz5zeta (Or.inr (by omega)) hz5theta
  have hct5 := primitiveQuarticChamberFace6001810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by omega) (by omega)
  have hq5 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hprim]
    omega
  rw [degreeZeroPrimitiveQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr5,
    add_zero] at hq5
  have hin5 : (-5 / 65536 : k) * A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff = 0 :=
    hct5.symm.trans hq5
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact quarticUnownedSystemBCFG11810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hin5 hAc hBc hFc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCFG` / `BG·BBB`: the 5 face rows force `b * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCFG15810_cert
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
/-- Unowned chamber `BCFG` / `BG·BBB` dies on the 5-carrier system (κ, ν, ο, π, Π). -/
theorem quarticChamberBCFG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG15810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
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
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
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
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
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
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
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
    kappaQuarticChamberRest6000810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz hEz (by omega) (by omega) hz0l hz0beta (Or.inr (by omega)) hz0delta hz0zeta (Or.inr (by omega)) hz0theta
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
  have hz1l : l = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hz1beta : beta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hz1delta : delta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
  have hz1theta : theta = 0 ∨ (2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
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
    nuQuarticChamberRest6000810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz hEz (by omega) (by omega) (by omega) (by omega) hz1l hz1beta (Or.inr (by omega)) hz1delta (Or.inr (by omega)) hz1zeta (Or.inr (by omega)) hz1theta
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
  have hz2l : l = 0 ∨ (7 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2beta : beta = 0 ∨ (6 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2delta : delta = 0 ∨ (5 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2zeta : zeta = 0 ∨ (4 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
  have hz2theta : theta = 0 ∨ (3 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
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
    omicronQuarticChamberRest6000810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hDz hEz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz2l hz2beta (Or.inr (by omega)) hz2delta (Or.inr (by omega)) hz2zeta (Or.inr (by omega)) hz2theta
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
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
    piQuarticChamberRest6000810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hDz hEz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz3l hz3beta (Or.inr (by omega)) hz3delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
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
  have hz4l : l = 0 ∨ (8 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 6 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz4beta : beta = 0 ∨ (7 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz4delta : delta = 0 ∨ (6 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz4zeta : zeta = 0 ∨ (5 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
  have hz4theta : theta = 0 ∨ (4 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
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
    primitiveQuarticChamberRest6000810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hDz hEz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz4l hz4beta (Or.inr (by omega)) hz4delta (Or.inr (by omega)) hz4zeta (Or.inr (by omega)) hz4theta
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
  exact quarticUnownedSystemBCFG15810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hBc hGc


end QuarticChamberUnownedSystems4810

end Max11DegreeRoutes
