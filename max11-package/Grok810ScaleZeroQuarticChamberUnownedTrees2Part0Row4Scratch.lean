import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedTreeRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeCertsScratch

/-! # Unowned plan trees, `(8,10)` scale zero

9 chambers that need a nested case split whose leaves include a
load kill (a load column alone on top forces `p = 0`) or a tied-load
top-coefficient system.  Every pivot orientation, every face and every
load-column verdict is re-derived here with the exact Farkas engine;
the cofactors are the plan's, rescaled to these rows and re-checked.
10 scalar certificates.  Untracked working note.
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

section QuarticChamberUnownedTrees2810

set_option maxHeartbeats 64000000 in
/-- Tree branch 4 of `quarticChamberBCFG7810_impossible`. -/
private theorem quarticChamberBCFG7810_impossible_row4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG7810 A B C D E F G)
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
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpv0 : B.natDegree + C.natDegree < 3 * A.natDegree)
    (hpv1 : B.natDegree + C.natDegree < 3 * A.natDegree)
    (hpv2 : 0 < B.natDegree) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have hdp21 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz21 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz21l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz21beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz21delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz21zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr21 : (kappaQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz21 hDz hEz hz21l hz21beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz21delta hz21zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy20 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroKappaQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr21, add_zero,
    kappaQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy20
  have hdp23 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz23 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz23l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz23beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz23delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr23 : (muQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz23 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz23l hz23beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz23delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy22 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroMuQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr23, add_zero,
    muQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy22
  have hdp25 : 0 < 2 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz25 : 0 < 2 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz25l : l = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz25beta : beta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz25delta : delta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz25zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr25 : (nuQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree :=
    nuQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz25 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz25l hz25beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz25delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz25zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy24 : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnu]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroNuQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr25, add_zero,
    nuQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy24
  have hdp27 : 0 < 3 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz27 : 0 < 3 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz27l : l = 0 ∨ (7 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz27beta : beta = 0 ∨ (6 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz27delta : delta = 0 ∨ (5 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz27zeta : zeta = 0 ∨ (4 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr27 : (omicronQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * A.natDegree + 3 * B.natDegree :=
    omicronQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz27 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz27l hz27beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz27delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz27zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy26 : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [homi]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroOmicronQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr27, add_zero,
    omicronQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy26
  have hdp29 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz29 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz29l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz29beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz29delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr29 : (piQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz29 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz29l hz29beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz29delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy28 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroPiQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr29, add_zero,
    piQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy28
  have hdp31 : A.natDegree < 4 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz31 : 0 < 4 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz31l : l = 0 ∨ (8 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 6 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz31beta : beta = 0 ∨ (7 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz31delta : delta = 0 ∨ (6 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz31zeta : zeta = 0 ∨ (5 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr31 : (primitiveQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * A.natDegree + 3 * B.natDegree :=
    primitiveQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz31 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz31l hz31beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz31delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz31zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy30 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hprim]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroPrimitiveQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr31, add_zero,
    primitiveQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy30
  have hdp33 : 0 < A.natDegree + 4 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz33 : 0 < A.natDegree + 4 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz33l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz33beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz33delta : delta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr33 : (xiQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 4 * B.natDegree :=
    xiQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz33 hDz hEz hz33l hz33beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz33delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy32 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroXiQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr33, add_zero,
    xiQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy32
  exact quarticUnownedTree4810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff  hsy20 hsy22 hsy24 hsy26 hsy28 hsy30 hsy32 hFc hGc

end QuarticChamberUnownedTrees2810

end Max11DegreeRoutes

