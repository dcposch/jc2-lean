import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedTreeRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreePiecesScratch
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
/-- Tree branch 3 of `quarticChamberBCFG7810_impossible`. -/
private theorem quarticChamberBCFG7810_impossible_row3
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
    (hpv2 : B.natDegree = 0) :
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
  have hdp1 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz1 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz1l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz1beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz1delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz1zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
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
  have hz1theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr1 : (kappaQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz hEz hz1l hz1beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz1delta hz1zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz1theta
  have hsy0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroKappaQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr1, add_zero,
    kappaQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy0
  have hdp3 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz3 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr3 : (muQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz3l hz3beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz3delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy2 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroMuQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr3, add_zero,
    muQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy2
  have hdp5 : A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz5 : 0 < A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz5l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 4 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz5beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz5delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz5zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
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
  have hz5theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hlf5 : (n3QuarticChamberRestLF9501810 A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree + C.natDegree :=
    n3QuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
      A B C D E F G hdz5 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)
  have hr5 : (n3QuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree + C.natDegree :=
    n3QuarticChamberRestOff1810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz5 hDz hEz hlf5 hz5l hz5beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz5delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz5zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz5theta
  have hsy4 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 hle; omega
  have hcc5 : (n3QuarticColumnTop1810 epsilon A B C D E F G).coeff
      (A.natDegree + 3 * B.natDegree + C.natDegree) =
      (3 / 64 : k) * epsilon * (A.leadingCoeff * B.leadingCoeff * C.leadingCoeff) + (-(3 / 32 : k)) * epsilon * (A.leadingCoeff * F.leadingCoeff) := by
    rw [show (A.natDegree + 3 * B.natDegree + C.natDegree) = (A.natDegree + B.natDegree + C.natDegree) from by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega]
    exact n3QuarticColumnTop1810_coeff epsilon hAne hBne hCne hFne (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)
  rw [degreeZeroN3Quartic810_eq_face9501_add_rest,
    n3QuarticChamberRest9501810_split1 l beta gamma delta epsilon zeta eta theta A B C D E F G,
    coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr5, add_zero,
    hcc5,
    n3QuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy4
  have hdp7 : A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz7 : 0 < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz7l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 6 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz7beta : beta = 0 ∨ (7 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz7delta : delta = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz7zeta : zeta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
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
  have hz7theta : theta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hlf7 : (n4QuarticChamberRestLF9502810 A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree :=
    n4QuarticChamberRestLF9502810_natDegree_lt_of_live_BCFG
      A B C D E F G hdz7 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)
  have hr7 : (n4QuarticChamberRestOff2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree :=
    n4QuarticChamberRestOff2810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz7 hDz hEz hlf7 hz7l hz7beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz7delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz7zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz7theta
  have hsy6 : (degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN4Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 hle; omega
  have hcc7 : (n4QuarticColumnTop2810 epsilon A B C D E F G).coeff
      (2 * A.natDegree + 3 * B.natDegree + C.natDegree) =
      (-(1 / 64 : k)) * epsilon * (A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff) + (1 / 32 : k) * epsilon * (A.leadingCoeff ^ 2 * F.leadingCoeff) := by
    rw [show (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = (2 * A.natDegree + B.natDegree + C.natDegree) from by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega]
    exact n4QuarticColumnTop2810_coeff epsilon hAne hBne hCne hFne (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)
  rw [degreeZeroN4Quartic810_eq_face9502_add_rest,
    n4QuarticChamberRest9502810_split2 l beta gamma delta epsilon zeta eta theta A B C D E F G,
    coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr7, add_zero,
    hcc7,
    n4QuarticChamberFace9502810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy6
  have hdp9 : 2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz9 : 0 < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz9l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 6 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz9beta : beta = 0 ∨ (7 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz9delta : delta = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz9zeta : zeta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
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
  have hz9theta : theta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr9 : (n6QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree :=
    n6QuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz9 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz9l hz9beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz9delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz9zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz9theta
  have hsy8 : (degreeZeroN6Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN6Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi hnu
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 hle; omega
  rw [degreeZeroN6Quartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr9, add_zero,
    n6QuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy8
  have hdp11 : 0 < 2 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz11 : 0 < 2 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz11l : l = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz11beta : beta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz11delta : delta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz11zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
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
  have hz11theta : theta = 0 ∨ (2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr11 : (nuQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree :=
    nuQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz11 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz11l hz11beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz11delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz11zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz11theta
  have hsy10 : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnu]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroNuQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr11, add_zero,
    nuQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy10
  have hdp13 : 0 < 3 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz13 : 0 < 3 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz13l : l = 0 ∨ (7 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz13beta : beta = 0 ∨ (6 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz13delta : delta = 0 ∨ (5 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz13zeta : zeta = 0 ∨ (4 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
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
  have hz13theta : theta = 0 ∨ (3 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr13 : (omicronQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * A.natDegree + 3 * B.natDegree :=
    omicronQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz13 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz13l hz13beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz13delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz13zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz13theta
  have hsy12 : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [homi]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroOmicronQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr13, add_zero,
    omicronQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy12
  have hdp15 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz15 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz15l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz15beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz15delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr15 : (piQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz15 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz15l hz15beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz15delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy14 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroPiQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr15, add_zero,
    piQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy14
  have hdp17 : A.natDegree < 4 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz17 : 0 < 4 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hz17l : l = 0 ∨ (8 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 6 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz17beta : beta = 0 ∨ (7 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz17delta : delta = 0 ∨ (6 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz17zeta : zeta = 0 ∨ (5 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
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
  have hz17theta : theta = 0 ∨ (4 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hr17 : (primitiveQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * A.natDegree + 3 * B.natDegree :=
    primitiveQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz17 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) hz17l hz17beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz17delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz17zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz17theta
  have hsy16 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hprim]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  rw [degreeZeroPrimitiveQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr17, add_zero,
    primitiveQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy16
  have hdp19 : 0 < A.natDegree + 4 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hdz19 : 0 < A.natDegree + 4 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz19l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz19beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hz19delta : delta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2 h; omega)
  have hlf19 : (xiQuarticChamberRestLF9501810 A B C D E F G).natDegree < A.natDegree + 4 * B.natDegree :=
    xiQuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
      A B C D E F G hdz19 hDz hEz
  have hr19 : (xiQuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 4 * B.natDegree :=
    xiQuarticChamberRestOff1810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz19 hDz hEz hlf19 hz19l hz19beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) hz19delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega))
  have hsy18 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega
  have hcc19 : (xiQuarticColumnTop1810 epsilon A B C D E F G).coeff
      (A.natDegree + 4 * B.natDegree) =
      (1 / 32 : k) * epsilon * (A.leadingCoeff * B.leadingCoeff ^ 2) + (-(1 / 8 : k)) * epsilon * (C.leadingCoeff ^ 2) + (1 / 2 : k) * epsilon * (G.leadingCoeff) := by
    rw [show (A.natDegree + 4 * B.natDegree) = (A.natDegree + 2 * B.natDegree) from by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega]
    exact xiQuarticColumnTop1810_coeff epsilon hAne hBne hCne hGne (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)
  rw [degreeZeroXiQuartic810_eq_face9501_add_rest,
    xiQuarticChamberRest9501810_split1 l beta gamma delta epsilon zeta eta theta A B C D E F G,
    coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr19, add_zero,
    hcc19,
    xiQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hpv1 hpv2; omega)] at hsy18
  exact quarticUnownedTree5810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff epsilon hsy0 hsy2 (by linear_combination hsy4) (by linear_combination hsy6) hsy8 hsy10 hsy12 hsy14 hsy16 (by linear_combination hsy18) hGc

end QuarticChamberUnownedTrees2810

end Max11DegreeRoutes

