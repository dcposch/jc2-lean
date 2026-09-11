import Grok810ScaleZeroQuarticChamberDefs2Scratch
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
/-- Tree branch 7 of `quarticChamberBCFG7810_impossible`. -/
private theorem quarticChamberBCFG7810_impossible_row7
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
    (hpv0 : B.natDegree + C.natDegree = 3 * A.natDegree) :
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
  have hdp35 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz35 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz35l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr35 : (kappaQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz35 hDz hEz hz35l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy34 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  rw [degreeZeroKappaQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr35, add_zero,
    kappaQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy34
  have hdp37 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz37 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz37l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr37 : (muQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz37 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz37l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy36 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  rw [degreeZeroMuQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr37, add_zero,
    muQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy36
  have hdp39 : A.natDegree < 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz39 : 0 < 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz39l : l = 0 ∨ (6 * A.natDegree < 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + C.natDegree < 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree < 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + G.natDegree < 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 3 * B.natDegree + C.natDegree ∧ 3 * C.natDegree < 3 * B.natDegree + C.natDegree ∧ C.natDegree + G.natDegree < 3 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr39 : (n2QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * B.natDegree + C.natDegree :=
    n2QuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz39 hDz hEz hz39l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy38 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr39, add_zero,
    n2QuarticChamberFace9501810_coeff_top hBne hCne hFne (A := A) (D := D) (E := E) (G := G) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy38
  have hdp41 : A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz41 : 0 < A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz41l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 4 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr41 : (n3QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree + C.natDegree :=
    n3QuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz41 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz41l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy40 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hle; omega
  rw [degreeZeroN3Quartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr41, add_zero,
    n3QuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy40
  have hdp43 : A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz43 : 0 < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz43l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 6 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr43 : (n4QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree :=
    n4QuarticChamberRest9502810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz43 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz43l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy42 : (degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN4Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hle; omega
  rw [degreeZeroN4Quartic810_eq_face9502_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr43, add_zero,
    n4QuarticChamberFace9502810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy42
  have hdp45 : 2 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz45 : 0 < A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz45l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 4 * B.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * F.natDegree < A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr45 : (n5QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree + C.natDegree :=
    n5QuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz45 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz45l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy44 : (degreeZeroN5Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN5Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu hkap
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hle; omega
  rw [degreeZeroN5Quartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr45, add_zero,
    n5QuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy44
  have hdp47 : 2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz47 : 0 < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz47l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 6 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr47 : (n6QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree :=
    n6QuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz47 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz47l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy46 : (degreeZeroN6Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN6Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi hnu
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hle; omega
  rw [degreeZeroN6Quartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr47, add_zero,
    n6QuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy46
  have hdp49 : 3 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz49 : 0 < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz49l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 6 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 3 * B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 4 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ A.natDegree + 2 * F.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr49 : (n7QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree :=
    n7QuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz49 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz49l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy48 : (degreeZeroN7Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN7Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi hnu hkap
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 hle; omega
  rw [degreeZeroN7Quartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr49, add_zero,
    n7QuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy48
  have hdp51 : 0 < 2 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz51 : 0 < 2 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz51l : l = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ C.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr51 : (nuQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree :=
    nuQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz51 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz51l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy50 : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnu]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  rw [degreeZeroNuQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr51, add_zero,
    nuQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy50
  have hdp53 : 0 < 3 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz53 : 0 < 3 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz53l : l = 0 ∨ (7 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 3 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr53 : (omicronQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * A.natDegree + 3 * B.natDegree :=
    omicronQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz53 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz53l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy52 : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [homi]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  rw [degreeZeroOmicronQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr53, add_zero,
    omicronQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy52
  have hdp55 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz55 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz55l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr55 : (piQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz55 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz55l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy54 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  rw [degreeZeroPiQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr55, add_zero,
    piQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy54
  have hdp57 : A.natDegree < 4 * A.natDegree + 3 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz57 : 0 < 4 * A.natDegree + 3 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz57l : l = 0 ∨ (8 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 6 * A.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree + C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * C.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr57 : (primitiveQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * A.natDegree + 3 * B.natDegree :=
    primitiveQuarticChamberRest9500810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz57 hDz hEz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) hz57l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy56 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hprim]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  rw [degreeZeroPrimitiveQuartic810_eq_face9500_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr57, add_zero,
    primitiveQuarticChamberFace9500810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy56
  have hdp59 : 0 < A.natDegree + 4 * B.natDegree := by
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  have hdz59 : 0 < A.natDegree + 4 * B.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hz59l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
    · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0 h; omega)
  have hr59 : (xiQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 4 * B.natDegree :=
    xiQuarticChamberRest9501810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz59 hDz hEz hz59l (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega))
  have hsy58 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega
  rw [degreeZeroXiQuartic810_eq_face9501_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr59, add_zero,
    xiQuarticChamberFace9501810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hpv0; omega)] at hsy58
  exact quarticUnownedTree3810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff  hsy34 hsy36 hsy38 hsy40 hsy42 hsy44 hsy46 hsy48 hsy50 hsy52 hsy54 hsy56 hsy58 hFc

end QuarticChamberUnownedTrees2810

end Max11DegreeRoutes

