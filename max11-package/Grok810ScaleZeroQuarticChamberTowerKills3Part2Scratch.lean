import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart00Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart21Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart22Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart23Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberTowerRests4Scratch
import Grok810ScaleZeroQuarticChamberTowerRests3Scratch
import Grok810ScaleZeroQuarticChamberTowerBridgesScratch

/-! # Tower deep-rescue chamber kills, part 3/4

4 of the 17 chambers `Grok810ScaleZeroQuarticTowerScratch` owns: the bridges of
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

section QuarticChamberTowerKills3810

set_option maxHeartbeats 64000000 in
/-- Tower deep-rescue `BCDFG15` on chamber `BCDFG` / `BF·BG·CF·CG·DD·BBB·BBC·BCC·CCC`, target `a*c*d^3`. -/
theorem quarticChamberBCDFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG9810 A B C D E F G)
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
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp0 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hdz0 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := hdp0
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4640 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4244 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4641 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4246 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4247 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4248 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4642 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4643 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4251 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4644 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4253 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq1 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4254 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4255 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4645 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4646 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4258 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4647 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4260 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4261 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4262 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4263 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4264 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4265 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
  have hr0 : (muQuarticChamberRest9005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9005810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hEz (by clear * - hcq1 hcq3 hcq4 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq1 hcq4 hcq8; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq8; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega))
  have hct0 := muQuarticChamberFace9005810_coeff_top hAne hBne hCne hDne hFne hGne (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face9005_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hs0 : (5 / 512 : k) * muQuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hin0 : muQuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp1 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    clear * - hApos; omega
  have hdz1 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := hdp1
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4648 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4649 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4650 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4651 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4652 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4653 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4654 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4655 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4656 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4657 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4658 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq1 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4659 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4660 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4661 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4662 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4663 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4664 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4665 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4666 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4667 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4668 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4669 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4670 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
  have hr1 : (xiQuarticChamberRest9006810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest9006810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hEz (by clear * - hcq1 hcq3 hcq4 hcq8; omega) (by clear * - hcq1 hcq3 hcq4 hcq8; omega) (by clear * - hcq1 hcq3 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq3 hcq8; omega) (by clear * - hcq3 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq1 hcq3 hcq4 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega))
  have hct1 := xiQuarticChamberFace9006810_coeff_top hAne hBne hCne hDne hFne (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face9006_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hs1 : (5 / 256 : k) * xiQuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hin1 : xiQuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hdz2 : 0 < 2 * A.natDegree + 4 * B.natDegree := hdp2
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4671 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4290 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4672 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4292 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4293 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4294 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4673 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4674 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4297 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4675 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4299 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq1 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4300 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4301 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4676 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4677 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4304 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4678 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4306 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4307 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4308 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4309 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4310 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4679 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
  have hr2 : (piQuarticChamberRest9005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9005810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hEz (by clear * - hcq8; omega) (by clear * - hcq1 hcq3 hcq4 hcq8; omega) (by clear * - hcq3 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq1 hcq8; omega) (by clear * - hcq0 hcq4 hcq8; omega) (by clear * - hcq1 hcq4 hcq8; omega) hz2l hz2beta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) hz2delta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega))
  have hct2 := piQuarticChamberFace9005810_coeff_top hAne hBne hCne hDne hFne hGne (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face9005_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hs2 : (5 / 4096 : k) * piQuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hin2 : piQuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp3 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hdz3 : 0 < A.natDegree + 3 * B.natDegree := hdp3
  have hz3l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4680 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4681 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4313 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4682 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4315 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4683 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz3beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4684 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4685 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4318 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4686 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4320 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4687 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz3delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4688 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4689 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4323 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4690 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4325 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4691 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4327 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4328 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4692 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
  have hz3zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4693 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4694 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4331 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4695 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4333 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4696 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4335 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4336 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4337 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4338 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4339 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
  have hz3theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4697 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4698 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq3 hcq8 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4699 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq1 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4343 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4700 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq3 hcq8 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_4345 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4346 A.natDegree B.natDegree D.natDegree F.natDegree h hcq4 hcq3 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4347 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4348 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq4 hcq3 hcq8)
  have hr3 : (kappaQuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9003810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hEz (by clear * - hcq8; omega) hz3l hz3beta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) hz3delta (Or.inr (by clear * - hcq8; omega)) hz3zeta (Or.inr (by clear * - hcq3 hcq4 hcq8; omega)) hz3theta
  have hct3 := kappaQuarticChamberFace9003810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega)
  have hq3 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp3
  rw [degreeZeroKappaQuartic810_eq_face9003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hs3 : (5 / 512 : k) * kappaQuarticCostChamberBCDEFG2Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hin3 : kappaQuarticCostChamberBCDEFG2Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs3 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp4 : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega
  have hdz4 : 0 < A.natDegree + 2 * B.natDegree + D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4; omega
  have hz4l : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4701 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4351 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4702 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4353 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4354 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4703 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4356 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4704 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4358 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4359 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4705 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4361 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4362 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4363 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4706 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz4beta : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4707 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4366 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4708 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4368 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4369 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4709 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4371 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4710 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4373 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4374 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4711 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4376 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4377 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4378 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4712 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz4delta : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4713 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4381 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4714 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4383 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4384 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4715 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4386 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4716 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4388 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4389 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4717 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4391 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4392 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4393 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4394 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4718 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4396 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4397 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4398 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4719 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq8)
  have hz4zeta : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4720 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4401 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4721 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4403 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4404 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4722 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4406 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4723 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4408 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4409 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4724 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4411 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4412 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4413 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4414 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4725 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4416 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4417 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4418 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4726 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4420 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4421 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4727 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
  have hz4theta : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4728 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4424 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4729 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4426 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4427 A.natDegree B.natDegree D.natDegree F.natDegree h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4730 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4429 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4731 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4431 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4432 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4732 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4434 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4435 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4436 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4437 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4733 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4439 A.natDegree B.natDegree D.natDegree F.natDegree h hcq4 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4440 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4441 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4734 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq3 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_4443 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4444 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4445 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4446 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq3 hcq8)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4447 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq3 hcq8)
  have hr4 : (n2QuarticChamberRest9004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + D.natDegree :=
    n2QuarticChamberRest9004810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hEz (by clear * - hcq1 hcq3 hcq4 hcq8; omega) (by clear * - hcq3 hcq8; omega) (by clear * - hcq8; omega) hz4l hz4beta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) hz4delta (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq8; omega)) hz4zeta (Or.inr (by clear * - hcq3 hcq4 hcq8; omega)) hz4theta
  have hct4 := n2QuarticChamberFace9004810_coeff_top hAne hBne hCne hDne hGne (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega)
  have hq4 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hs4 : (5 / 512 : k) * n2QuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct4.symm.trans hq4
  have hin4 : n2QuarticCostChamberBCDEFG5Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs4 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticCostChamberBCDFG15810_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hAc hBc hCc hDc hFc hGc

end QuarticChamberTowerKills3810

end Max11DegreeRoutes
