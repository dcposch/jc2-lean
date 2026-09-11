import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch

/-! # Unowned multi-carrier systems, part 13/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems13810

set_option maxHeartbeats 64000000 in
/-- Carrier row 1 of `quarticRefinedBCDEFG102L5810_impossible`. -/
private theorem quarticRefinedBCDEFG102L5810_impossible_row1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L5810 A B C D E F G)
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
          A B C D E F G).natDegree = 0) :
    (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0
    := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
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
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz1 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1 h; omega)
  have hr1 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) hz1l hz1beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega))
  have hct1 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp1 hdz1; omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  exact hin1

end QuarticChamberUnownedSystems13810

end Max11DegreeRoutes
/-! # Unowned multi-carrier systems, part 13/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems13810

set_option maxHeartbeats 64000000 in
/-- Carrier row 5 of `quarticRefinedBCDEFG102L5810_impossible`. -/
private theorem quarticRefinedBCDEFG102L5810_impossible_row5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L5810 A B C D E F G)
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
          A B C D E F G).natDegree = 0) :
    (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0
    := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
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
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp5 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz5 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5; omega
  have hz5l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
  have hz5beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
    · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5 h; omega)
  have hr5 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz5 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) hz5l hz5beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega))
  have hct5 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega)
  have hq5 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp5 hdz5; omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr5,
    add_zero] at hq5
  have hin5 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct5.symm.trans hq5
  exact hin5

end QuarticChamberUnownedSystems13810

end Max11DegreeRoutes
