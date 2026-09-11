import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch

/-! # Unowned multi-carrier systems, part 5/15

6 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems5810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCFG` / `BG·CG·BBB·BBC·BCC·CCC`: the 6 face rows force `b * c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCFG17810_cert
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
/-- Unowned chamber `BCFG` / `BG·CG·BBB·BBC·BCC·CCC` dies on the 6-carrier system (κ, μ, ν, ο, π, Π). -/
theorem quarticChamberBCFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG17810 A B C D E F G)
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
      · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hApos; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq6 hcq9; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq1 hcq8 hcq9; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq9; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq8 hcq9; omega)
  have hr0 : (kappaQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6002810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz hEz (by clear * - hcq1 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6002810_coeff_top hAne hBne hCne hGne (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6002_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hApos; omega)
  have hr1 : (muQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest6002810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz hEz (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hct1 := muQuarticChamberFace6002810_coeff_top hAne hBne hCne hGne (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroMuQuartic810_eq_face6002_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1; omega
  have hdz4 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4; omega
  have hz4l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
  have hz4beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
  have hz4delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq0 hcq1 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hApos; omega)
  have hr4 : (piQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6003810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hDz hEz (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq0 hcq6 hcq9; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz4l hz4beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz4delta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hct4 := piQuarticChamberFace6003810_coeff_top hAne hBne hCne hGne (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega)
  have hq4 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdz0 hdp1 hdz1 hdp4 hdz4; omega
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
/-- The Singular-lifted certificate of chamber `CDEG` / `CG·CCC`: the 2 face rows force `c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDEG2810_cert
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
/-- Unowned chamber `CDEG` / `CG·CCC` dies on the 2-carrier system (μ, π). -/
theorem quarticChamberCDEG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn; omega
  have hdz0 : 0 < 3 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq6; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq6; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq6; omega)
  have hr0 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hFz (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct0 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega
  have hdz1 : 0 < 4 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq6; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq6; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
  have hr1 : (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6001810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hFz (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq1 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace6001810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega
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
/-- The Singular-lifted certificate of chamber `CDEG` / `CG·DD·CCC`: the 4 face rows force `a * d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDEG4810_cert
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
/-- Unowned chamber `CDEG` / `CG·DD·CCC` dies on the 4-carrier system (μ, π, N₃, N₄). -/
theorem quarticChamberCDEG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG4810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hz0delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    · exact absurd h (by clear * - hFn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hr0 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hFz (by clear * - hcq0 hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2; omega))
  have hct0 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz1delta : delta = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hr1 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hFz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2; omega))
  have hct1 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAF hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAF hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq3; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hApos; omega)
  have hr2 : (n3QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest6000810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz hFz (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq3; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz2zeta (Or.inr (by clear * - hcq0 hcq1 hcq2; omega)) hz2theta
  have hct2 := n3QuarticChamberFace6000810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
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
set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CDEG` / `CG·EE·CCC`: the 3 face rows force `e * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDEG10810_cert
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
/-- Unowned chamber `CDEG` / `CG·EE·CCC` dies on the 3-carrier system (μ, ξ, π). -/
theorem quarticChamberCDEG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG10810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn; omega
  have hdz0 : 0 < 3 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hr0 : (muQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6004810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hFz (by clear * - hcq1 hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq1 hcq2; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega))
  have hct0 := muQuarticChamberFace6004810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff + (5 / 32 : k) * E.leadingCoeff ^ 2 = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 2 * C.natDegree + E.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0; omega
  have hdz1 : 0 < 2 * C.natDegree + E.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hr1 : (xiQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest6000810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hFz (by clear * - hcq0 hcq2 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega))
  have hct1 := xiQuarticChamberFace6000810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroXiQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (-15 / 128 : k) * C.leadingCoeff ^ 2 * E.leadingCoeff + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 4 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < 4 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
  have hr2 : (piQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6005810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz hFz (by clear * - hcq1 hcq2; omega) (by clear * - hcq1 hcq2 hcq5; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega))
  have hct2 := piQuarticChamberFace6005810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega
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
/-- The Singular-lifted certificate of chamber `CDFG` / `CG·CCC`: the 2 face rows force `c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDFG14810_cert
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
/-- Unowned chamber `CDFG` / `CG·CCC` dies on the 2-carrier system (μ, π). -/
theorem quarticChamberCDFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn; omega
  have hdz0 : 0 < 3 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq7; omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hr0 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hEz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq7; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0; omega
  have hdz1 : 0 < 4 * C.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq7; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hr1 : (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6001810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hEz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq2 hcq7; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace6001810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega
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
/-- The Singular-lifted certificate of chamber `CDFG` / `CG·DD·CCC`: the 4 face rows force `a * d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDFG16810_cert
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
/-- Unowned chamber `CDFG` / `CG·DD·CCC` dies on the 4-carrier system (μ, π, N₃, N₄). -/
theorem quarticChamberCDFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG16810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
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
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz0delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hr0 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hEz (by clear * - hcq0 hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hr1 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hEz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz2beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz2delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz2zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hz2theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
  have hr2 : (n3QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest6000810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz hEz (by clear * - hcq0 hcq3; omega) (by clear * - hcq4; omega) (by clear * - hcq0 hcq1 hcq3; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz2zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz2theta
  have hct2 := n3QuarticChamberFace6000810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
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


end QuarticChamberUnownedSystems5810

end Max11DegreeRoutes
