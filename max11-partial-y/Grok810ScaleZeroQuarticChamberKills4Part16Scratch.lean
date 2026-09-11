import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests4Scratch
import Grok810ScaleZeroQuarticChamberInnerScratch

/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEG` / `CG·EE·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq2 hcq3 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hr0 : (kappaQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest10810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz (by clear * - hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq2; omega))
  have hct0 := kappaQuarticChamberFace10810_coeff_top hBne hCne hGne (A := A) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face10_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq2 hcq3 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hr1 : (muQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest11810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by clear * - hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq2 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega))
  have hct1 := muQuarticChamberFace11810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 4 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq2 hcq3 hApos hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ 5 * B.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + 3 * C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * E.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hr2 : (piQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest4810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz hFz (by clear * - hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq2 hcq3; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega))
  have hct2 := piQuarticChamberFace4810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1 hdp2; omega
  rw [degreeZeroPiQuartic810_eq_face4_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticNoTargetInner_BCEG_zero_impossible B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hBc hCc hEc hGc

end QuarticChamberKills4810

end Max11DegreeRoutes
