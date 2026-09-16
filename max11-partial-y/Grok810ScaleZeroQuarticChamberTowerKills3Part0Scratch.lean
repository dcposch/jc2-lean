import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart00Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart21Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart22Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
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
