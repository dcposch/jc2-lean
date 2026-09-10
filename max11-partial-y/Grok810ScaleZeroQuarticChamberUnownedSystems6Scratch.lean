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

/-! # Unowned multi-carrier systems, part 6/15

4 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems6810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CEFG` / `CG·CCC`: the 2 face rows force `c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCEFG14810_cert
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
/-- Unowned chamber `CEFG` / `CG·CCC` dies on the 2-carrier system (μ, π). -/
theorem quarticChamberCEFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn; omega
  have hdz0 : 0 < 3 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0; omega
  have hz0l : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq7; omega)
  have hz0beta : beta = 0 ∨ (A.natDegree + F.natDegree < 3 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hApos; omega)
    · exact Or.inr (by clear * - h hcq1 hcq7; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq7; omega)
  have hr0 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hDz (by clear * - hcq0 hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct0 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0; omega
  have hdz1 : 0 < 4 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ E.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
  have hr1 : (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6001810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hDz (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq2; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace6001810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : C.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((3 / 5 : k) * C.leadingCoeff ^ 2 + (8 / 5 : k) * G.leadingCoeff) * hin0 + ((2 / 5 : k) * C.leadingCoeff) * hin1
  exact (mul_ne_zero hCc (pow_ne_zero 2 hGc)) ht
set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CEFG` / `CG·EE·CCC`: the 3 face rows force `e * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCEFG16810_cert
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
/-- Unowned chamber `CEFG` / `CG·EE·CCC` dies on the 3-carrier system (μ, ξ, π). -/
theorem quarticChamberCEFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG16810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn; omega
  have hdz0 : 0 < 3 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0; omega
  have hz0l : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz0beta : beta = 0 ∨ (A.natDegree + F.natDegree < 3 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hr0 : (muQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6004810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hDz hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega))
  have hct0 := muQuarticChamberFace6004810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff + (5 / 32 : k) * E.leadingCoeff ^ 2 = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 2 * C.natDegree + E.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0; omega
  have hdz1 : 0 < 2 * C.natDegree + E.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz1delta : delta = 0 ∨ (A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hr1 : (xiQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest6000810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hDz (by clear * - hcq0 hcq1 hcq2 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega))
  have hct1 := xiQuarticChamberFace6000810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroXiQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (-15 / 128 : k) * C.leadingCoeff ^ 2 * E.leadingCoeff + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 4 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < 4 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ E.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hr2 : (piQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6005810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz hDz (by clear * - hcq1 hcq2; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq1 hcq2; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega))
  have hct2 := piQuarticChamberFace6005810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega
  rw [degreeZeroPiQuartic810_eq_face6005_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (-5 / 8 : k) * C.leadingCoeff * E.leadingCoeff ^ 2 + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct2.symm.trans hq2
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : E.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * C.leadingCoeff * E.leadingCoeff) * hin0 + ((-3 / 11 : k) * C.leadingCoeff ^ 2 + (104 / 55 : k) * G.leadingCoeff) * hin1 + ((18 / 55 : k) * E.leadingCoeff) * hin2
  exact (mul_ne_zero hEc (pow_ne_zero 2 hGc)) ht
set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CDEFG` / `CF·CG·DD·DE·EE`: the 4 face rows force `e * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDEFG8810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 64 : k) * a * d * f + (5 / 16 : k) * e * g = 0)
    (hr1 : (-5 / 16 : k) * a * f ^ 2 + (5 / 4 : k) * g ^ 2 = 0)
    (hr2 : (-15 / 256 : k) * a * d * g + (-15 / 256 : k) * a * e * f = 0)
    (hr3 : (5 / 256 : k) * a ^ 2 * d * g + (5 / 256 : k) * a ^ 2 * e * f = 0)
    (hEc : (e : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : e * g ^ 2 = 0 := by
    linear_combination ((8 / 5 : k) * g) * hr0 + ((2 / 5 : k) * e) * hr1 + ((-32 / 15 : k) * f) * hr2
  exact (mul_ne_zero hEc (pow_ne_zero 2 hGc)) ht
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEFG` / `CF·CG·DD·DE·EE` dies on the 4-carrier system (ξ, π, N₃, N₄). -/
theorem quarticChamberCDEFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG8810 A B C D E F G)
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
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp0 : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn; omega
  have hdz0 : 0 < A.natDegree + D.natDegree + F.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
  have hr0 : (xiQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest6001810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz (by clear * - hcq1 hcq2 hcq11; omega) (by clear * - hcq0 hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq5; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq11; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega))
  have hct0 := xiQuarticChamberFace6001810_coeff_top hAne hDne hEne hFne hGne (B := B) (C := C) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0; omega)
  have hq0 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0; omega
  rw [degreeZeroXiQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 64 : k) * A.leadingCoeff * D.leadingCoeff * F.leadingCoeff + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + 2 * F.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hr1 : (piQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest6006810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz (by clear * - hcq1 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq5 hcq11; omega) (by clear * - hcq1 hcq2 hcq11; omega) (by clear * - hcq0 hcq2 hcq5 hcq11; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq11; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega))
  have hct1 := piQuarticChamberFace6006810_coeff_top hAne hFne hGne (B := B) (C := C) (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6006_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (-5 / 16 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < A.natDegree + D.natDegree + G.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < A.natDegree + D.natDegree + G.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * C.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz2beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz2delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz2zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hz2theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq11; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq11; omega)
  have hr2 : (n3QuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + G.natDegree :=
    n3QuarticChamberRest6001810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq2 hcq5 hcq11; omega) (by clear * - hcq0 hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq5; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq11; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) hz2zeta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) hz2theta
  have hct2 := n3QuarticChamberFace6001810_coeff_top hAne hDne hEne hFne hGne (B := B) (C := C) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + G.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
  rw [degreeZeroN3Quartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (-15 / 256 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff + (-15 / 256 : k) * A.leadingCoeff * E.leadingCoeff * F.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : E.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((8 / 5 : k) * G.leadingCoeff) * hin0 + ((2 / 5 : k) * E.leadingCoeff) * hin1 + ((-32 / 15 : k) * F.leadingCoeff) * hin2
  exact (mul_ne_zero hEc (pow_ne_zero 2 hGc)) ht
set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDEG` / `CG·DD·CCC` leaf 0: the 5 face rows force `d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCDEG30L0810_cert
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
/-- Unowned chamber `BCDEG` / `CG·DD·CCC` leaf 0 dies on the 5-carrier system (μ, π, N₂, N₃, N₄). -/
theorem quarticRefinedBCDEG30L0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEG30L0810 A B C D E F G)
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
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11 hApos; omega)
  have hr0 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hFz (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11; omega) hz0l hz0beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11 hApos; omega)) hz0delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11 hApos; omega))
  have hct0 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11 hApos; omega)
  have hr1 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hFz (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq4 hx10 hx11; omega) hz1l hz1beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11 hApos; omega)) hz1delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11 hApos; omega))
  have hct1 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < 2 * C.natDegree + D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < 2 * C.natDegree + D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz2zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
  have hz2theta : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)
  have hr2 : (n2QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest6000810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hFz (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hx10 hx11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq2 hcq4 hx10 hx11; omega) hz2l hz2beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hx10 hx11 hApos; omega)) hz2delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)) hz2zeta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq4 hx10 hx11; omega)) hz2theta
  have hct2 := n2QuarticChamberFace6000810_coeff_top hCne hDne hGne (A := A) (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
  rw [degreeZeroN2Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : D.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * C.leadingCoeff * D.leadingCoeff) * hin0 + ((18 / 55 : k) * D.leadingCoeff) * hin1 + ((-3 / 11 : k) * C.leadingCoeff ^ 2 + (104 / 55 : k) * G.leadingCoeff) * hin2
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht


end QuarticChamberUnownedSystems6810

end Max11DegreeRoutes
