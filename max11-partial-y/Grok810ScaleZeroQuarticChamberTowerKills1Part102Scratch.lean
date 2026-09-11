import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberTowerRests2Scratch
import Grok810ScaleZeroQuarticChamberTowerBridgesScratch

/-! # Tower deep-rescue chamber kills, part 1/4

6 of the 17 chambers `Grok810ScaleZeroQuarticTowerScratch` owns: the bridges of
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

section QuarticChamberTowerKills1810

set_option maxHeartbeats 64000000 in
/-- Tower deep-rescue `BCDEFG12` on chamber `BCDEFG` / `CG·DD·CCC` leaf 4, target `a*c*d^3`. -/
theorem quarticRefinedBCDEFG102L4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L4810 A B C D E F G)
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
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
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
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)
  have hr0 : (muQuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest9003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) hz0l hz0beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) hz0delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega))
  have hct0 := muQuarticChamberFace9003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hs0 : (5 / 128 : k) * muQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hin0 : muQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq4 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq4 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq4 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)
  have hr1 : (piQuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest9003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) hz1l hz1beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) hz1delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega))
  have hct1 := piQuarticChamberFace9003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hs1 : (5 / 256 : k) * piQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hin1 : piQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp2 : A.natDegree < 2 * C.natDegree + D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < 2 * C.natDegree + D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + F.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz2zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz2theta : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hr2 : (n2QuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest9003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) hz2l hz2beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) hz2delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) hz2zeta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)) hz2theta
  have hct2 := n2QuarticChamberFace9003810_coeff_top hCne hDne hGne (A := A) (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hs2 : (5 / 128 : k) * n2QuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hin2 : n2QuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticCostChamberBCDEFG12810_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hAc hBc hCc hDc hEc hFc hGc

end QuarticChamberTowerKills1810

end Max11DegreeRoutes
/-! # Tower deep-rescue chamber kills, part 1/4

6 of the 17 chambers `Grok810ScaleZeroQuarticTowerScratch` owns: the bridges of
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

section QuarticChamberTowerKills1810

set_option maxHeartbeats 64000000 in
/-- Tower deep-rescue `BCDEFG12` on chamber `BCDEFG` / `CG·DD·CCC` leaf 12, target `a*c*d^3`. -/
theorem quarticRefinedBCDEFG102L12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L12810 A B C D E F G)
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
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
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
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hr0 : (muQuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest9003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) hz0l (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega))
  have hct0 := muQuarticChamberFace9003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hs0 : (5 / 128 : k) * muQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hin0 : muQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq4 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hr1 : (piQuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest9003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) hz1l (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega))
  have hct1 := piQuarticChamberFace9003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hs1 : (5 / 256 : k) * piQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hin1 : piQuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp2 : A.natDegree < 2 * C.natDegree + D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < 2 * C.natDegree + D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + F.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq6 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)
  have hr2 : (n2QuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest9003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq6 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hcq5 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega) hz2l hz2beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) hz2delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq2 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hApos; omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26; omega)) (Or.inr (by omega))
  have hct2 := n2QuarticChamberFace9003810_coeff_top hCne hDne hGne (A := A) (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hs2 : (5 / 128 : k) * n2QuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hin2 : n2QuarticCostChamberBCDEFG12Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticCostChamberBCDEFG12810_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hAc hBc hCc hDc hEc hFc hGc

end QuarticChamberTowerKills1810

end Max11DegreeRoutes
