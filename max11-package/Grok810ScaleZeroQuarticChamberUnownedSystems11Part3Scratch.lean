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
import Grok810ScaleZeroQuarticChamberUnownedSystems11Part2Scratch

/-! # Unowned multi-carrier systems, part 11/15

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

section QuarticChamberUnownedSystems11810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEFG` / `CG·DD·CCC` leaf 4 dies on the 4-carrier system (μ, π, N₃, N₄). -/
theorem quarticRefinedCDEFG28L4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedCDEFG28L4810 A B C D E F G)
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
  obtain ⟨hcell, hx0⟩ := hch
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hcell
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
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hx0 hApos; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hx0 hApos; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
  have hz0delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hx0 hApos; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq2 hApos; omega)
  have hr0 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz (by clear * - hx0 hcq0 hcq4; omega) (by clear * - hx0 hcq0 hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hApos; omega)) hz0delta (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hx0 hcq0 hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0; omega) (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hx0 hApos; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hx0 hApos; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hx0 hApos; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq2 hcq3 hApos; omega)
  have hr1 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz (by clear * - hx0 hcq0 hcq1 hcq2; omega) (by clear * - hx0 hcq0 hcq4; omega) (by clear * - hx0 hcq0 hcq3; omega) (by clear * - hx0 hcq0 hcq3 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hApos; omega)) hz1delta (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree := by
    clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  have hz2beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  have hz2delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
  have hz2zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
  have hz2theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hx0 hcq0 hcq1 hcq5; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hcq0 hcq1 hcq3 hApos; omega)
  have hr2 : (n3QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest6000810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz (by clear * - hx0 hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hx0 hcq0 hcq4; omega) (by clear * - hx0 hcq0 hcq3 hcq5; omega) (by clear * - hx0 hcq5; omega) (by clear * - hx0 hcq0 hcq1 hcq4; omega) hz2l hz2beta (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hApos; omega)) hz2delta (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hApos; omega)) hz2zeta (Or.inr (by clear * - hx0 hcq0 hcq1 hcq2 hApos; omega)) hz2theta
  have hct2 := n3QuarticChamberFace6000810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    clear * - hx0 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
  rw [degreeZeroN3Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (45 / 2048 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-15 / 256 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : A.leadingCoeff * D.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff) * hin0 + ((18 / 55 : k) * A.leadingCoeff * D.leadingCoeff) * hin1 + ((16 / 11 : k) * C.leadingCoeff ^ 2 + (-1664 / 165 : k) * G.leadingCoeff) * hin2
  exact (mul_ne_zero (mul_ne_zero hAc hDc) (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems11810

end Max11DegreeRoutes
