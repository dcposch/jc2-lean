import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
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
/-- Carrier row 0 of `quarticChamberBCDEFG11810_impossible`. -/
private theorem quarticChamberBCDEFG11810_impossible_row0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    xiQuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0
    := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hdp0 : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz0 : 0 < A.natDegree + D.natDegree + F.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hr0 : (xiQuarticChamberRest9007810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest9007810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 (by clear * - hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq3 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq3 hcq6 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq6 hcq14; omega) (by clear * - hcq3 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq6 hcq14; omega))
  have hct0 := xiQuarticChamberFace9007810_coeff_top hAne hDne hEne hFne hGne (B := B) (C := C) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega)
  have hq0 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega
  rw [degreeZeroXiQuartic810_eq_face9007_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hs0 : (5 / 64 : k) * xiQuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hin0 : xiQuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact hin0

end QuarticChamberTowerKills2810

end Max11DegreeRoutes
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
/-- Carrier row 1 of `quarticChamberBCDEFG11810_impossible`. -/
private theorem quarticChamberBCDEFG11810_impossible_row1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    piQuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0
    := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hdp1 : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz1 : 0 < A.natDegree + 2 * F.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hr1 : (piQuarticChamberRest9006810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest9006810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq6 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq4 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega) (by clear * - hcq1 hcq6 hcq14; omega) (by clear * - hcq6 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq6 hcq14; omega) (by clear * - hcq3 hcq4 hcq14; omega) (by clear * - hcq1 hcq4 hcq6 hcq14; omega) hz1l hz1beta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega)) hz1delta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq6 hcq14; omega))
  have hct1 := piQuarticChamberFace9006810_coeff_top hAne hFne hGne (B := B) (C := C) (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face9006_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hs1 : (5 / 16 : k) * piQuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hin1 : piQuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact hin1

end QuarticChamberTowerKills2810

end Max11DegreeRoutes
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
/-- Carrier row 2 of `quarticChamberBCDEFG11810_impossible`. -/
private theorem quarticChamberBCDEFG11810_impossible_row2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    n2QuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0
    := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hdp2 : A.natDegree < D.natDegree + G.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz2 : 0 < D.natDegree + G.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp2; omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 4 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 3 * C.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * E.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * C.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz2zeta : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree < D.natDegree + G.natDegree ∧ E.natDegree < D.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq6 hcq14; omega)
  have hz2theta : theta = 0 ∨ (2 * A.natDegree < D.natDegree + G.natDegree ∧ C.natDegree < D.natDegree + G.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq14; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq6 hcq14; omega)
  have hr2 : (n2QuarticChamberRest9005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    n2QuarticChamberRest9005810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq0 hcq3 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hcq14; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega)) hz2zeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega)) hz2theta
  have hct2 := n2QuarticChamberFace9005810_coeff_top hDne hEne hFne hGne (A := A) (B := B) (C := C) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp2 hdz2; omega)
  have hq2 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (D.natDegree + G.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp2 hdz2 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9005_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hs2 : (5 / 16 : k) * n2QuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hin2 : n2QuarticCostChamberBCDEFG6Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact hin2

end QuarticChamberTowerKills2810

end Max11DegreeRoutes
