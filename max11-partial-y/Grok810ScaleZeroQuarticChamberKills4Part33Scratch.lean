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
/-- Chamber `BCEFG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
    by_contra hzero
    exact hnc (by clear * - hAB hDn hcq0 hcq3 hcq4 hcq7 hApos hcq10 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq4 hcq5 hcq14; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq4 hcq14; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq14; omega)
      · exact Or.inr (by clear * - h hAB hAD hDn hcq0; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos hcq14; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq14; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq14; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hcq14; omega)
    · exact Or.inr (by clear * - h hAB hDn hApos; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos hcq14; omega)
    · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hApos hcq14; omega)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq4; omega) (by clear * - hcq5; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hDn hcq0 hcq3 hcq4 hcq7 hApos hcq10 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos hcq14; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq4 hcq5 hcq14; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq5 hcq14; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq4; omega) (by clear * - hcq0 hcq7; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq5 hcq7 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face3_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticChamberInnerSystem0810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc

end QuarticChamberKills4810

end Max11DegreeRoutes
