import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberTowerRests2Scratch
import Grok810ScaleZeroQuarticChamberTowerBridgesScratch

/-! # Tower deep-rescue chamber kills, part 2/4

5 of the 17 chambers `Grok810ScaleZeroQuarticTowerScratch` owns: the bridges of
`…ChamberTowerBridgesScratch` feed the tower's own scalar
`quarticCostChamber<tag>810_impossible`.  Every face is checked to be
the tower's face (exactly, up to the recorded rational scale) and every
load column carries a Farkas certificate.  Untracked working note.
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

section QuarticChamberTowerKills2810

set_option maxHeartbeats 64000000 in
/-- Carrier row 3 of `quarticChamberBCDEFG15810_impossible`. -/
private theorem quarticChamberBCDEFG15810_impossible_row3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    kappaQuarticCostChamberBCDEFG2Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0
    := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp3 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz3 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp3; omega
  have hz3l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq8 hcq13; omega)
  have hz3beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq8 hcq13; omega)
  have hz3delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
  have hz3zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
  have hz3theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4 hcq8 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq8 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq8 hcq13; omega)
  have hr3 : (kappaQuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 (by clear * - hcq0 hcq3 hcq8 hcq13; omega) (by clear * - hcq3 hcq4 hcq8; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq8 hcq13; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq8 hcq13; omega)) hz3zeta (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq8 hcq13; omega)) hz3theta
  have hct3 := kappaQuarticChamberFace9003810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp3 hdz3; omega)
  have hq3 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp3 hdz3; omega
  rw [degreeZeroKappaQuartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hs3 : (5 / 512 : k) * kappaQuarticCostChamberBCDEFG2Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hin3 : kappaQuarticCostChamberBCDEFG2Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs3 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact hin3

end QuarticChamberTowerKills2810

end Max11DegreeRoutes
