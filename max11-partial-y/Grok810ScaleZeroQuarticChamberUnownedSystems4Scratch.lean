import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch

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
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hApos; omega)
  have hr0 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hEz hFz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hApos; omega)
  have hr1 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hEz hFz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq0 hcq2 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < 2 * C.natDegree + D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < 2 * C.natDegree + D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2theta : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hr2 : (n2QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest6000810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hEz hFz (by clear * - hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq2 hcq3; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz2zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz2theta
  have hct2 := n2QuarticChamberFace6000810_coeff_top hCne hDne hGne (A := A) (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
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
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn; omega
  have hdz0 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
    · exact Or.inr (by clear * - h hEn hcq7; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq7; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
  have hr0 : (kappaQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6001810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz hEz (by clear * - hcq0 hcq1 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6001810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hr1 : (muQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest6001810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz hEz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace6001810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroMuQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 64 : k) * A.leadingCoeff * B.leadingCoeff * F.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 = 0 :=
    hct1.symm.trans hq1
  have hdp4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega
  have hdz4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4; omega
  have hz4l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
  have hz4beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hz4delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hr4 : (piQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6002810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hDz hEz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz4l hz4beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz4delta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct4 := piQuarticChamberFace6002810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega)
  have hq4 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega
  rw [degreeZeroPiQuartic810_eq_face6002_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hin4 : (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (-45 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (5 / 32 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-5 / 16 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 = 0 :=
    hct4.symm.trans hq4
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have ht : A.leadingCoeff * B.leadingCoeff * F.leadingCoeff ^ 3 = 0 := by
    linear_combination ((-1 / 10 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff + (1 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * F.leadingCoeff + (-4 / 15 : k) * C.leadingCoeff ^ 2 * F.leadingCoeff) * hin0 + ((2 / 5 : k) * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (-16 / 5 : k) * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-32 / 15 : k) * F.leadingCoeff ^ 2) * hin1 + ((4 / 15 : k) * B.leadingCoeff ^ 2 * C.leadingCoeff + (-8 / 3 : k) * B.leadingCoeff * F.leadingCoeff) * hin4
  exact (mul_ne_zero (mul_ne_zero hAc hBc) (pow_ne_zero 3 hFc)) ht
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
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn; omega
  have hdz0 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq6; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hApos; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq3 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hApos; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq5; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq6; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq3 hcq6; omega)
    · exact Or.inr (by clear * - h hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq3 hcq5 hcq6; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6; omega)
  have hr0 : (kappaQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6000810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz hEz (by clear * - hcq3; omega) (by clear * - hcq0 hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq3; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega
  have hdz3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp3; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq6; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq6 hApos; omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hApos; omega)
  have hr3 : (piQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6000810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hDz hEz (by clear * - hcq3; omega) (by clear * - hcq0 hcq3 hcq6; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq5; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hct3 := piQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp3 hdz3; omega)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp3 hdz3; omega
  rw [degreeZeroPiQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (5 / 64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct3.symm.trans hq3
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : B.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((-3 / 20 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 + (8 / 5 : k) * G.leadingCoeff) * hin0 + ((2 / 5 : k) * B.leadingCoeff) * hin3
  exact (mul_ne_zero hBc (pow_ne_zero 2 hGc)) ht


end QuarticChamberUnownedSystems4810

end Max11DegreeRoutes
