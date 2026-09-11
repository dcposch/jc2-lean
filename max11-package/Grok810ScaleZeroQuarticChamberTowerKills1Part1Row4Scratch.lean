import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberTowerRests1Scratch
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
/-- Carrier row 4 of `quarticChamberBCDEFG58810_impossible`. -/
private theorem quarticChamberBCDEFG58810_impossible_row4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG58810 A B C D E F G)
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
    n2QuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0
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
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp4 : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz4 : 0 < A.natDegree + 2 * B.natDegree + D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp4; omega
  have hz4l : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq9 hcq11; omega)
  have hz4beta : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq9 hcq11; omega)
  have hz4delta : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq11; omega)
  have hz4zeta : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq11; omega)
  have hz4theta : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
  have hr4 : (n2QuarticChamberRest9001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + D.natDegree :=
    n2QuarticChamberRest9001810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 (by clear * - hcq0 hcq1 hcq4 hcq11; omega) (by clear * - hcq0 hcq1 hcq9 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9; omega) hz4l hz4beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9 hcq11; omega)) hz4delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9 hcq11; omega)) hz4zeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9 hcq11; omega)) hz4theta
  have hct4 := n2QuarticChamberFace9001810_coeff_top hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp4 hdz4; omega)
  have hq4 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp4 hdz4 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hs4 : (5 / 512 : k) * n2QuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct4.symm.trans hq4
  have hin4 : n2QuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs4 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact hin4

end QuarticChamberTowerKills1810

end Max11DegreeRoutes
