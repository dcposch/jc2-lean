import Grok810ScaleZeroQuarticChamberDefs1Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch

/-! # Unowned multi-carrier systems, part 2/15

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

section QuarticChamberUnownedSystems2810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCG` / `BG·CG·BBB·BBC·BCC·CCC`: the 6 face rows force `b * c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCG5810_cert
    (a b c d e f g : k)
    (hr0 : (5 / 512 : k) * a * b ^ 3 + (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * b * g = 0)
    (hr1 : (15 / 512 : k) * a * b ^ 2 * c + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr2 : (-5 / 4096 : k) * a ^ 2 * b ^ 3 + (15 / 1024 : k) * a * b * c ^ 2 + (-5 / 128 : k) * a * b * g = 0)
    (hr3 : (-5 / 65536 : k) * a ^ 3 * b ^ 3 + (15 / 16384 : k) * a ^ 2 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 2 * b * g = 0)
    (hr4 : (15 / 4096 : k) * a ^ 2 * b ^ 4 + (-45 / 512 : k) * a * b ^ 2 * c ^ 2 + (5 / 64 : k) * a * b ^ 2 * g + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr5 : (-5 / 65536 : k) * a ^ 4 * b ^ 3 + (15 / 16384 : k) * a ^ 3 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 3 * b * g = 0)
    (hBc : (b : k) ≠ 0)
    (hCc : (c : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : b * c * g ^ 2 = 0 := by
    linear_combination ((-1 / 5 : k) * a * b ^ 2 * c + (8 / 15 : k) * c * g) * hr0 + ((4 / 5 : k) * b * c ^ 2 + (8 / 15 : k) * b * g) * hr1 + ((8 / 15 : k) * b * c) * hr4
  exact (mul_ne_zero (mul_ne_zero hBc hCc) (pow_ne_zero 2 hGc)) ht
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCG` / `BG·CG·BBB·BBC·BCC·CCC` dies on the 6-carrier system (κ, μ, ν, ο, π, Π). -/
theorem quarticChamberBCG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCG5810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
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
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn; omega
  have hdz0 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hApos; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hFn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hEn hFn hApos; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq1 hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
  have hr0 : (kappaQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6002810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz hEz hFz hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6002810_coeff_top hAne hBne hCne hGne (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6002_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hr1 : (muQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest6002810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz hEz hFz (by clear * - hcq0 hcq1 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace6002810_coeff_top hAne hBne hCne hGne (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroMuQuartic810_eq_face6002_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1; omega
  have hdz4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1 hdp4; omega
  have hz4l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz4beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz4delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hr4 : (piQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6003810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hDz hEz hFz (by clear * - hcq0 hcq1 hcq5; omega) hz4l hz4beta (Or.inr (by clear * - hcq0 hApos; omega)) hz4delta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct4 := piQuarticChamberFace6003810_coeff_top hAne hBne hCne hGne (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega)
  have hq4 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega
  rw [degreeZeroPiQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hin4 : (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (-45 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (5 / 64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct4.symm.trans hq4
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : B.leadingCoeff * C.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((-1 / 5 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (8 / 15 : k) * C.leadingCoeff * G.leadingCoeff) * hin0 + ((4 / 5 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (8 / 15 : k) * B.leadingCoeff * G.leadingCoeff) * hin1 + ((8 / 15 : k) * B.leadingCoeff * C.leadingCoeff) * hin4
  exact (mul_ne_zero (mul_ne_zero hBc hCc) (pow_ne_zero 2 hGc)) ht
set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCG` / `CG·CCC`: the 6 face rows force `b * c * g = 0`. -/
theorem quarticUnownedSystemBCG10810_cert
    (a b c d e f g : k)
    (hr0 : (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * b * g = 0)
    (hr1 : (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr2 : (15 / 1024 : k) * a * b * c ^ 2 + (-5 / 128 : k) * a * b * g = 0)
    (hr3 : (15 / 16384 : k) * a ^ 2 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 2 * b * g = 0)
    (hr4 : (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr5 : (15 / 16384 : k) * a ^ 3 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 3 * b * g = 0)
    (hBc : (b : k) ≠ 0)
    (hCc : (c : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : b * c * g = 0 := by
    linear_combination ((-8 / 5 : k) * c) * hr0 + ((24 / 5 : k) * b) * hr1
  exact (mul_ne_zero (mul_ne_zero hBc hCc) hGc) ht
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCG` / `CG·CCC` dies on the 6-carrier system (κ, μ, ν, ο, π, Π). -/
theorem quarticChamberBCG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCG10810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn; omega
  have hdz0 : 0 < B.natDegree + 2 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq2; omega)
      · exact Or.inr (by clear * - h hEn hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2; omega)
  have hr0 : (kappaQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest6003810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz hEz hFz (by clear * - hcq1; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1; omega))
  have hct0 := kappaQuarticChamberFace6003810_coeff_top hBne hCne hGne (A := A) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 3 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0; omega
  have hdz1 : 0 < 3 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hApos; omega)
  have hr1 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz hEz hFz (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq2; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz1delta (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hct1 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : B.leadingCoeff * C.leadingCoeff * G.leadingCoeff = 0 := by
    linear_combination ((-8 / 5 : k) * C.leadingCoeff) * hin0 + ((24 / 5 : k) * B.leadingCoeff) * hin1
  exact (mul_ne_zero (mul_ne_zero hBc hCc) hGc) ht
set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BDG` / `BG·BBB`: the 5 face rows force `b * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBDG2810_cert
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
/-- Unowned chamber `BDG` / `BG·BBB` dies on the 5-carrier system (κ, ν, ο, π, Π). -/
theorem quarticChamberBDG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDG2810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
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
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn; omega
  have hdz0 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hCn hEn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hApos; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2; omega)
    · exact Or.inr (by clear * - h hEn hFn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq2; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hEn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq2; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2; omega)
    · exact Or.inr (by clear * - h hEn hFn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq2; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hEn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq2; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
  have hr0 : (kappaQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6000810_natDegree_lt_of_live_BDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hCz hEz hFz (by clear * - hcq2; omega) hz0l hz0beta hz0delta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq2; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0 hdz0; omega
  have hdz3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0 hdz0 hdp3; omega
  have hz3l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
  have hz3beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2; omega)
  have hr3 : (piQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6000810_natDegree_lt_of_live_BDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hCz hEz hFz (by clear * - hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq2; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct3 := piQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0 hdz0 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0 hdz0 hdp3 hdz3; omega)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hFn hdp0 hdz0 hdp3 hdz3; omega
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


end QuarticChamberUnownedSystems2810

end Max11DegreeRoutes
