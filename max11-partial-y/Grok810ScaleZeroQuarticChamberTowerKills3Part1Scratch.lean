import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart00Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart21Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart22Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart23Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
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
/-- Tower deep-rescue `BCDEG13` on chamber `BCDEG` / `BG·CG·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*d^3*g^2`. -/
theorem quarticChamberBCDEG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG10810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4448 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4449 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4450 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4451 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4452 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4453 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4454 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4455 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4456 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4457 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4458 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq0 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4459 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4460 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4461 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4462 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4463 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4464 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4465 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4466 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4467 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4468 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4469 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4470 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
  have hr0 : (muQuarticChamberRest9001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9001810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hFz (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq8; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega))
  have hct0 := muQuarticChamberFace9001810_coeff_top hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face9001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hs0 : (5 / 512 : k) * muQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hin0 : muQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := hdp1
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4471 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4472 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAF hcq0 hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4268 A.natDegree B.natDegree D.natDegree E.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4473 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4474 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4475 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq2 hcq8 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4476 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4477 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4478 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4275 A.natDegree B.natDegree D.natDegree E.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4479 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4480 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4481 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq2 hcq8 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4482 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4483 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4484 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4282 A.natDegree B.natDegree D.natDegree E.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4485 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4486 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4487 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4488 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4489 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4490 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq2 hcq8 hcq4)
  have hr1 : (xiQuarticChamberRest9001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest9001810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hFz (by clear * - hcq2 hcq4 hcq8; omega) (by clear * - hcq2 hcq4 hcq8; omega) (by clear * - hcq0 hcq2 hcq4 hcq8; omega) (by clear * - hcq2 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq2 hcq4 hcq8; omega))
  have hct1 := xiQuarticChamberFace9001810_coeff_top hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face9001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hs1 : (5 / 512 : k) * xiQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hin1 : xiQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hdz2 : 0 < 2 * A.natDegree + 4 * B.natDegree := hdp2
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4491 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4492 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4493 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4494 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4495 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4496 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4497 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4498 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4499 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4500 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4501 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq0 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4502 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4503 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4504 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4505 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4506 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4507 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4508 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4509 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4510 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4511 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4512 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4513 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq2 hcq8 hcq4)
  have hr2 : (piQuarticChamberRest9001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9001810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hFz (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq4 hcq8; omega) (by clear * - hcq2 hcq4 hcq8; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega))
  have hct2 := piQuarticChamberFace9001810_coeff_top hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face9001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hs2 : (5 / 4096 : k) * piQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hin2 : piQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp3 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hdz3 : 0 < A.natDegree + 3 * B.natDegree := hdp3
  have hz3l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0343 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4514 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAF hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4515 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4516 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4517 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4518 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz3beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0350 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4519 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAF hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4520 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4521 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4522 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4523 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz3delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0357 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4524 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4525 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4526 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4527 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4528 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4529 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4530 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4531 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz3zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0366 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4532 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq2 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4533 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4534 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4535 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4536 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4537 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4538 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4539 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4540 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4541 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
  have hz3theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0377 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4542 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq2 hcq8 hFn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4543 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq8 hFn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4544 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq2 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_4545 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4546 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq2 hcq8 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4547 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4548 A.natDegree B.natDegree D.natDegree G.natDegree h hcq1 hcq8 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4549 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq8 hFn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4550 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_4551 A.natDegree B.natDegree D.natDegree G.natDegree h hcq1 hcq8 hcq4)
  have hr3 : (kappaQuarticChamberRest9001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9001810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hFz (by clear * - hcq8; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) hz3delta (Or.inr (by clear * - hcq8; omega)) hz3zeta (Or.inr (by clear * - hcq1 hcq4 hcq8; omega)) hz3theta
  have hct3 := kappaQuarticChamberFace9001810_coeff_top hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega)
  have hq3 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp3
  rw [degreeZeroKappaQuartic810_eq_face9001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hs3 : (5 / 512 : k) * kappaQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hin3 : kappaQuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs3 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp4 : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega
  have hdz4 : 0 < A.natDegree + 2 * B.natDegree + D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4; omega
  have hz4l : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4552 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAF h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4553 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4554 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4353 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4555 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAF h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4556 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4557 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAF h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4558 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4358 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4559 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4560 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4561 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4562 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4563 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4564 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz4beta : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4565 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4566 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4567 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4368 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4568 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4569 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4570 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4571 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4373 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4572 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4573 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4574 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4575 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4576 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4577 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz4delta : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4578 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4579 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4580 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4383 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4581 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4582 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4583 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4584 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4388 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4585 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4586 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4587 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4588 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4589 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4590 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4591 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4592 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4593 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4594 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4595 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz4zeta : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4596 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4597 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4598 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4403 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4599 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAF hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4600 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4601 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4602 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4408 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4603 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4604 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4605 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4606 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4607 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4608 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4609 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4610 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4611 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4612 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4613 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4614 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4615 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4616 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8 hcq4)
  have hz4theta : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4617 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4618 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4619 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4426 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4620 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4621 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4622 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4623 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4431 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_4624 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4625 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4626 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4627 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4628 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4629 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4630 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4631 A.natDegree B.natDegree D.natDegree G.natDegree h hcq1 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4632 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4633 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4634 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq2 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4635 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4636 A.natDegree B.natDegree D.natDegree G.natDegree hcq1 h hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4637 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq8 hFn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_4638 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 h hcq0 hcq8 hcq4)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4639 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
  have hr4 : (n2QuarticChamberRest9001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + D.natDegree :=
    n2QuarticChamberRest9001810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hFz (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq8; omega) hz4l hz4beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) hz4delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) hz4zeta (Or.inr (by clear * - hcq1 hcq4 hcq8; omega)) hz4theta
  have hct4 := n2QuarticChamberFace9001810_coeff_top hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega)
  have hq4 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hs4 : (5 / 512 : k) * n2QuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct4.symm.trans hq4
  have hin4 : n2QuarticCostChamberBCDEFG10Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs4 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticCostChamberBCDEG13810_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hAc hBc hCc hDc hEc hGc

end QuarticChamberTowerKills3810

end Max11DegreeRoutes
