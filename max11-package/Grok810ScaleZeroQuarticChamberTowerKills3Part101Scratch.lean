import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart101Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart107Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart108Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberTowerRests3Scratch
import Grok810ScaleZeroQuarticChamberTowerBridgesScratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberTowerRests4Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch

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
/-- Tower deep-rescue `BCDEFG9` on chamber `BCDEFG` / `BF·CF·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*c*d*f^3`. -/
theorem quarticChamberBCDEFG34810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG34810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4243 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4244 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4245 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4246 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4247 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4248 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4249 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4250 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4251 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4252 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4253 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq0 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4254 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4255 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4256 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq1 hcq10)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4257 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4258 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4259 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4260 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4261 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4262 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4263 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4264 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4265 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
  have hr0 : (muQuarticChamberRest9000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 (by clear * - hcq0 hcq1 hcq4 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq0 hcq4 hcq10; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9 hcq10; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq10; omega))
  have hct0 := muQuarticChamberFace9000810_coeff_top hAne hBne hCne hDne hEne hFne (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face9000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hs0 : (5 / 512 : k) * muQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hin0 : muQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := hdp1
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4266 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4267 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4268 A.natDegree B.natDegree D.natDegree E.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4269 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4270 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4271 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4272 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4273 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4274 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4275 A.natDegree B.natDegree D.natDegree E.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4276 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 hcq2 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4277 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4278 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4279 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq1 hcq10)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4280 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4281 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4282 A.natDegree B.natDegree D.natDegree E.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4283 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4284 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4285 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4286 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4287 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq1 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4288 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq2 hcq0 hcq1 hcq10)
  have hr1 : (xiQuarticChamberRest9000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest9000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 (by clear * - hcq2 hcq4 hcq10; omega) (by clear * - hcq2 hcq4 hcq10; omega) (by clear * - hcq0 hcq2 hcq4 hcq10; omega) (by clear * - hcq0 hcq2 hcq9 hcq10; omega) (by clear * - hcq0 hcq2 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq2 hcq4 hcq10; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq10; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq4 hcq10; omega)) (Or.inr (by clear * - hcq2 hcq4 hcq10; omega))
  have hct1 := xiQuarticChamberFace9000810_coeff_top hAne hBne hCne hDne hEne hFne (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face9000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hs1 : (5 / 512 : k) * xiQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hin1 : xiQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hdz2 : 0 < 2 * A.natDegree + 4 * B.natDegree := hdp2
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4289 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4290 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4291 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4292 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4293 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4294 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4295 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4296 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4297 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4298 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4299 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq0 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4300 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4301 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4302 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq1 hcq10)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4303 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4304 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4305 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4306 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4307 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4308 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4309 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4310 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4311 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq2 hcq0 hcq1 hcq10)
  have hr2 : (piQuarticChamberRest9000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq4 hcq10; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq10; omega) (by clear * - hcq0 hcq4 hcq9 hcq10; omega) (by clear * - hcq1 hcq2 hcq4 hcq10; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq0 hcq4 hcq10; omega) (by clear * - hcq2 hcq4 hcq10; omega) (by clear * - hcq0 hcq4 hcq9; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq10; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq10; omega))
  have hct2 := piQuarticChamberFace9000810_coeff_top hAne hBne hCne hDne hEne hFne (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face9000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hs2 : (5 / 4096 : k) * piQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hin2 : piQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp3 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hdz3 : 0 < A.natDegree + 3 * B.natDegree := hdp3
  have hz3l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0916 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4312 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4313 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4314 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4315 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4316 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz3beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0918 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4317 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4318 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4319 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4320 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4321 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz3delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0920 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4322 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4323 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4324 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4325 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4326 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4327 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4328 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4329 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq1 hcq10)
  have hz3zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0921 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4330 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4331 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4332 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4333 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4334 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4335 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4336 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4337 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4338 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4339 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
  have hz3theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0922 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq9 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4340 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq2 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4342 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4343 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4344 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq2 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4345 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4346 A.natDegree B.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4347 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4348 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_4349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq10)
  have hr3 : (kappaQuarticChamberRest9000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 (by clear * - hcq10; omega) (by clear * - hcq0 hcq4 hcq9; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq10; omega)) hz3delta (Or.inr (by clear * - hcq10; omega)) hz3zeta (Or.inr (by clear * - hcq1 hcq4 hcq10; omega)) hz3theta
  have hct3 := kappaQuarticChamberFace9000810_coeff_top hAne hBne hCne hDne hEne hFne (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega)
  have hq3 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp3
  rw [degreeZeroKappaQuartic810_eq_face9000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hs3 : (5 / 512 : k) * kappaQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hin3 : kappaQuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs3 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp4 : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega
  have hdz4 : 0 < A.natDegree + 2 * B.natDegree + D.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4; omega
  have hz4l : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 4 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4350 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4351 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4352 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4353 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4354 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4355 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4356 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4357 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4358 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4359 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4360 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4361 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4362 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4363 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4364 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz4beta : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4365 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4366 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4367 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4368 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4369 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4370 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4371 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4372 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4373 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4374 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4375 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4376 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4377 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4378 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4379 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz4delta : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4380 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4381 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4382 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4383 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4384 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4385 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4386 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4387 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4388 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4389 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4390 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4391 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4392 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4393 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4394 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4395 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4396 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4397 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4398 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4399 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq2 hcq0 hcq1 hcq9 hcq10)
  have hz4zeta : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ 2 * B.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ E.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4400 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4401 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4402 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4403 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4404 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4405 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4406 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4407 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4408 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4409 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4410 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4411 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4412 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4413 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4414 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4415 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4416 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4417 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4418 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4419 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4420 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4421 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4422 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq0 hcq1 hcq10)
  have hz4theta : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree ∧ C.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4423 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4424 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4425 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4426 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4427 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4428 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4429 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4430 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4431 A.natDegree B.natDegree D.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4432 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4433 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4434 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4435 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4436 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4437 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4438 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4439 A.natDegree B.natDegree D.natDegree F.natDegree h hcq4 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4440 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4441 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4442 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4443 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4444 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4445 A.natDegree B.natDegree D.natDegree F.natDegree hcq4 h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4446 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 h hcq0 hcq1 hcq10)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4447 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq4 hcq0 hcq1 hcq10)
  have hr4 : (n2QuarticChamberRest9000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + D.natDegree :=
    n2QuarticChamberRest9000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 (by clear * - hcq0 hcq1 hcq4 hcq10; omega) (by clear * - hcq1 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq4 hcq9; omega) hz4l hz4beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq10; omega)) hz4delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq10; omega)) hz4zeta (Or.inr (by clear * - hcq1 hcq4 hcq10; omega)) hz4theta
  have hct4 := n2QuarticChamberFace9000810_coeff_top hAne hBne hCne hDne hEne hFne (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega)
  have hq4 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hs4 : (5 / 512 : k) * n2QuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct4.symm.trans hq4
  have hin4 : n2QuarticCostChamberBCDEF1Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs4 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticCostChamberBCDEFG9810_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hAc hBc hCc hDc hEc hFc hGc

end QuarticChamberTowerKills3810

end Max11DegreeRoutes
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
/-- Tower deep-rescue `BCEFG17` on chamber `BCEFG` / `BF·BG·CF·CG·EE·BBB·BBC·BCC·CCC`, target `c*e^3`. -/
theorem quarticChamberBCEFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG9810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
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
  have hdp0 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hdz0 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := hdp0
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4735 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4736 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4737 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4738 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4739 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4740 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4741 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4742 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4743 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4744 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4745 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq1 hcq0 hcq3 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4746 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4747 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4748 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4749 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4750 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4751 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4752 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4753 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4754 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4755 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4756 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4757 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
  have hr0 : (muQuarticChamberRest9006810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9006810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hDz (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega) (by clear * - hcq0 hcq1 hcq9; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega))
  have hct0 := muQuarticChamberFace9006810_coeff_top hAne hBne hCne hEne hFne hGne (D := D) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face9006_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hs0 : (5 / 512 : k) * muQuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hin0 : muQuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := hdp1
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4758 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4759 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0794 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4760 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4761 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4762 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4763 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4764 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4765 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0801 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4766 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4767 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4768 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4769 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
  have hr1 : (xiQuarticChamberRest9008810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest9008810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hDz (by clear * - hcq0 hcq3 hcq4 hcq9; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega) (by clear * - hcq3 hcq9; omega) (by clear * - hcq0 hcq1 hcq3 hcq9; omega) (by clear * - hcq0 hcq3 hcq4 hcq9; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq9; omega))
  have hct1 := xiQuarticChamberFace9008810_coeff_top hAne hBne hCne hEne hGne (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face9008_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hs1 : (5 / 512 : k) * xiQuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hin1 : xiQuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hdz2 : 0 < 2 * A.natDegree + 4 * B.natDegree := hdp2
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4770 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4771 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4772 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4773 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4774 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4775 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4776 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4777 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4778 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4779 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4780 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq1 hcq0 hcq3 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4781 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4782 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4783 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4784 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4785 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4786 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4787 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4788 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4789 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4790 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4791 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4792 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
  have hr2 : (piQuarticChamberRest9007810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9007810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hDz (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega) (by clear * - hcq0 hcq3 hcq9; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq4 hcq9; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega))
  have hct2 := piQuarticChamberFace9007810_coeff_top hAne hBne hCne hEne hFne hGne (D := D) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face9007_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hs2 : (5 / 4096 : k) * piQuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hin2 : piQuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdp3 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hdz3 : 0 < A.natDegree + 3 * B.natDegree := hdp3
  have hz3l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0735 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hcq4 hAD h hcq0 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0736 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0737 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0738 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4793 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0740 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4794 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4795 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4796 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz3beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0744 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hcq4 hAD h hcq0 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0745 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0746 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0747 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4797 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0749 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4798 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4799 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4800 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz3delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0753 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hcq4 h hAD hcq0 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0754 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0755 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0756 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4801 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0758 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4802 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4803 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0761 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4804 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hAD hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0763 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4805 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz3zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0765 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0766 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0767 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0768 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4806 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0770 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4807 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4808 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0773 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4809 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0775 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 hcq3 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0776 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4810 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4811 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
  have hz3theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0778 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq3 hDn hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0779 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0780 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 hcq3 h hDn hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0781 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_4812 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0783 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq3 hDn hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_4813 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hDn hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_4814 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0786 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq3 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_4815 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hDn hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0788 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq3 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0789 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_4816 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0791 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq3 hDn hcq9)
  have hr3 : (kappaQuarticChamberRest9003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9003810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hDz hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) hz3delta hz3zeta (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq9; omega)) hz3theta
  have hct3 := kappaQuarticChamberFace9003810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega)
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
  have hdp4 : A.natDegree < B.natDegree + C.natDegree + E.natDegree := by
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3; omega
  have hdz4 : 0 < B.natDegree + C.natDegree + E.natDegree := by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4; omega
  have hz4l : l = 0 ∨ (6 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 4 * A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * A.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 4 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + G.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * B.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ C.natDegree + G.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * E.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4817 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4818 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4819 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4820 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4821 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4822 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4823 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4824 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4825 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4826 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4827 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4828 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4829 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4830 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4831 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz4beta : beta = 0 ∨ (5 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4832 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4833 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4834 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4835 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4836 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4837 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4838 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4839 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4840 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq4 hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4841 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4842 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4843 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4844 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4845 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4846 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz4delta : delta = 0 ∨ (4 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ G.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4847 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4848 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4849 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4850 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4851 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4852 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4853 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4854 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4855 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4856 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4857 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4858 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAD h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4859 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4860 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq1 hcq0 hcq3 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4861 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4862 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hAD h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4863 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4864 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hAD h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4865 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4866 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz4zeta : zeta = 0 ∨ (3 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ E.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4867 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4868 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4869 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4870 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4871 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4872 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4873 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4874 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4875 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4876 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4877 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4878 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4879 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4880 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4881 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4882 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hAD hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4883 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq1 hcq0 hcq3 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4884 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hAD hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4885 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4886 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4887 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hAD hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4888 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4889 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
  have hz4theta : theta = 0 ∨ (2 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ C.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4890 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4891 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4892 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4893 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq4 hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4894 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4895 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4896 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4897 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4898 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hcq1 hcq3 h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4899 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4900 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4901 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4902 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4903 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4904 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4905 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4906 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4907 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hAD hcq1 hcq0 hcq3 hDn hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4908 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4909 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4910 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1 hcq3 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_4911 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq1 hcq0 hcq3 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4912 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_4913 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq9)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4914 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq9)
  have hr4 : (n2QuarticChamberRest9006810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + C.natDegree + E.natDegree :=
    n2QuarticChamberRest9006810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hDz (by clear * - hcq0 hcq3 hcq4 hcq9; omega) (by clear * - hcq0 hcq1 hcq3 hcq9; omega) hz4l hz4beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) hz4delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9; omega)) hz4zeta hz4theta
  have hct4 := n2QuarticChamberFace9006810_coeff_top hBne hCne hEne hFne (A := A) (D := D) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4; omega)
  have hq4 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + C.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hdp3 hdz3 hdp4 hdz4 hle; omega
  rw [degreeZeroN2Quartic810_eq_face9006_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hs4 : (5 / 64 : k) * n2QuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct4.symm.trans hq4
  have hin4 : n2QuarticCostChamberBCDEFG7Face810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    rcases mul_eq_zero.mp hs4 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticCostChamberBCEFG17810_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hAc hBc hCc hEc hFc hGc


end QuarticChamberTowerKills3810

end Max11DegreeRoutes
