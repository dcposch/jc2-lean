import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart15Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart16Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart18Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart19Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart20Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart21Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberRests6Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberRests2Scratch

/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

set_option maxHeartbeats 64000000 in
/-- Refined leaf 7 of chamber `BCDEFG` / `CG·DD·CCC` dies on power system `S25`. -/
theorem quarticRefinedBCDEFG102L7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16, hrf17, hrf18, hrf19, hrf20, hrf21, hrf22, hrf23, hrf24, hrf25, hrf26, hrf27, hrf28, hrf29, hrf30, hrf31, hrf32⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hrf0 hrf2 hrf5 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * D.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3151 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4052 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hrf0 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3153 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4053 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3155 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3156 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3157 A.natDegree B.natDegree C.natDegree D.natDegree h hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3158 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4054 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf0 hrf2 hcq0 hrf5 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3160 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4055 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hrf0 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3162 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4056 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3164 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3165 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3166 A.natDegree B.natDegree C.natDegree D.natDegree h hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3167 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3168 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hrf0 hcq0 hrf5 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3169 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4057 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hrf0 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3171 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4058 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3173 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3174 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3175 A.natDegree B.natDegree C.natDegree D.natDegree h hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3176 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3177 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3178 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3179 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4059 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3181 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4060 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hrf0 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3183 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4061 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3185 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3186 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3187 A.natDegree B.natDegree C.natDegree D.natDegree h hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3188 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3189 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3190 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3191 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 h hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4062 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3193 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3194 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
  have hr0 : (kappaQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest15810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq3; omega) (by clear * - hcq3 hrf5; omega) (by clear * - hcq1 hrf2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega)) hz0delta (Or.inr (by clear * - hcq3 hrf5; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq3; omega))
  have hct0 := kappaQuarticChamberFace15810_coeff_top_S25 hBne hCne hDne hEne hGne (A := A) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face15_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3195 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3196 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3197 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3198 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4063 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3200 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4064 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf2 hcq0 hrf5 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3202 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3203 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3204 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3205 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4065 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3207 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4066 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf2 hcq0 hrf5 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3209 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3210 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3211 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3212 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4067 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3214 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4068 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
  have hr1 : (muQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest19810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq3 hrf2; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq3 hrf2 hrf5; omega) (by clear * - hcq0 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega))
  have hct1 := muQuarticChamberFace19810_coeff_top_S25 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega)
  have hqq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : muQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hdp2 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3216 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4069 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3218 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hrf0 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3219 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3220 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3221 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4070 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf0 hrf2 hcq0 hrf5 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3223 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4071 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3225 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hrf0 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3226 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 h hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3227 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3228 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4072 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf0 hrf2 hcq0 hrf5 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3230 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4073 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3232 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hrf0 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_3233 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3234 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3235 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4074 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3237 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4075 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf2 hcq0 hrf5 hcq1)
  have hr2 : (xiQuarticChamberRest21810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest21810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq3 hcq5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq1 hrf2; omega) (by clear * - hcq0 hcq3 hrf5; omega) (by clear * - hcq0 hcq3 hrf2 hrf5; omega) (by clear * - hcq0 hcq3 hcq5 hrf5; omega) (by clear * - hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf0 hrf2 hrf5; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf0 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega))
  have hct2 := xiQuarticChamberFace21810_coeff_top_S25 hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega)
  have hqq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face21_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hqq2
  have hin2 : xiQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hqq2
  have hdp3 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3239 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3240 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3241 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3242 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4076 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3243 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4077 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf0 hrf2 hcq0 hrf5 hcq1)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3245 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3246 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3247 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3248 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4078 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3249 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4079 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf0 hrf2 hcq0 hrf5 hcq1)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3251 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3252 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3253 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3254 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq5 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4080 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hrf2 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3255 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hrf5 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4081 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hrf2 hcq0 hrf5 hcq1)
  have hr3 : (piQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest13810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq3 hrf2; omega) (by clear * - hcq0 hcq3 hcq5; omega) (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf2; omega) (by clear * - hcq0 hcq3 hrf5; omega) (by clear * - hcq0 hcq3 hcq5 hrf2 hrf5; omega) (by clear * - hcq0 hcq3 hrf2 hrf5; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq3 hcq5 hrf5; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hrf2 hrf5; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hrf2 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hrf2 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega))
  have hct3 := piQuarticChamberFace13810_coeff_top_S25 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega)
  have hqq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hqq3
  have hin3 : piQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hqq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS25810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hBc hCc hDc hEc hGc

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

set_option maxHeartbeats 64000000 in
/-- Refined leaf 11 of chamber `BCDEFG` / `CG·DD·CCC` dies on power system `S34`. -/
theorem quarticRefinedBCDEFG102L11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16, hrf17, hrf18, hrf19, hrf20, hrf21, hrf22, hrf23, hrf24, hrf25, hrf26, hrf27, hrf28, hrf29, hrf30, hrf31, hrf32, hrf33, hrf34, hrf35⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hdp0 : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6 hcq7 hrf0 hrf1 hrf5 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4082 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4083 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4084 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4085 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4086 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4087 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4088 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4089 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4090 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4091 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4092 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf0 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4093 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4094 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4095 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4096 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4097 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4098 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4099 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4100 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4101 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4102 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4103 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4104 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4105 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4106 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4107 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4108 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4109 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4110 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4112 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4113 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4114 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4115 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4116 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4117 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4118 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4119 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4120 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4121 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4122 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4123 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4124 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4125 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
  have hr0 : (kappaQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest14810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq1 hcq4 hrf1; omega) (by clear * - hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq1 hrf1; omega) (by clear * - hrf1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq4 hrf1 hrf5; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq1 hcq4 hrf1; omega))
  have hct0 := kappaQuarticChamberFace14810_coeff_top_S34 hCne hDne hEne hFne (A := A) (B := B) (G := G) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (C.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4126 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4127 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4128 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4129 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4130 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4131 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4133 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4134 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4135 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4136 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4137 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4138 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4139 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4140 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4141 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4142 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4143 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4144 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4145 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4146 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
  have hr1 : (muQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest19810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by clear * - hcq0 hcq1 hcq4 hrf1; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq4 hrf1; omega) (by clear * - hcq0 hcq1 hcq4 hcq5 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq4 hrf5; omega) (by clear * - hcq0 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq5 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega))
  have hct1 := muQuarticChamberFace19810_coeff_top_S34 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega)
  have hqq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : muQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hdp2 : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4147 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4148 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4149 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf0 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4150 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4151 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4152 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4153 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4154 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4155 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4156 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf0 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4157 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4158 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4159 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4160 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4161 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4162 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4163 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4164 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4165 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4166 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4167 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4168 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0 hrf5 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4169 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hr2 : (xiQuarticChamberRest23810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest23810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1; omega) (by clear * - hcq1 hrf1; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1 hrf5; omega) (by clear * - hcq1 hrf5; omega) (by clear * - hcq0 hcq4 hrf5; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1 hrf5; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega))
  have hct2 := xiQuarticChamberFace23810_coeff_top_S34 hAne hCne hDne hEne hFne hGne (B := B) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega)
  have hqq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face23_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hqq2
  have hin2 : xiQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hqq2
  have hdp3 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4170 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3834 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4171 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4172 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4173 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4174 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4175 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4176 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3840 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4177 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4178 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4179 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4180 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4181 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hrf0 hcq0 hrf5 hcq1)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4182 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hrf1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3846 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4183 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4184 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4185 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
      · exact Or.inr (astra4u_Round4Package_nat_4186 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq0 hrf5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4187 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq4 hrf1 hcq0 hrf5 hcq1)
  have hr3 : (piQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest13810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by clear * - hcq0 hcq1 hcq4 hrf1; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf1; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq4 hrf1; omega) (by clear * - hcq0 hcq4 hrf1; omega) (by clear * - hcq0 hcq4 hcq5 hrf1; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hcq5 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq4 hrf1 hrf5; omega) (by clear * - hcq0 hcq4 hcq5 hrf1 hrf5; omega) (by clear * - hcq0 hcq4 hrf5; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq4 hcq5 hrf5; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq5 hrf1 hrf5; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq5 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq5 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf1 hrf5; omega))
  have hct3 := piQuarticChamberFace13810_coeff_top_S34 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega)
  have hqq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hqq3
  have hin3 : piQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hqq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS34810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hCc hDc hEc hFc hGc

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

set_option maxHeartbeats 64000000 in
/-- Refined leaf 13 of chamber `BCDEFG` / `CG·DD·CCC` dies on the single-monomial `ξ` face. -/
theorem quarticRefinedBCDEFG102L13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16, hrf17, hrf18, hrf19, hrf20, hrf21, hrf22, hrf23, hrf24, hrf25, hrf26⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < C.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq6 hcq7 hrf0 hrf1 hrf6 hApos hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4188 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4189 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4190 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf0 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4191 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4192 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4193 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4194 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hrf0 hcq0 hcq1)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4195 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4196 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4197 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf0 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_4198 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hrf7 h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4199 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4200 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4201 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hrf7 hrf1 hrf0 hcq0 hcq1)
  have hr0 : (xiQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq0 hcq1 hcq7 hrf1 hrf7; omega) (by clear * - hcq0 hcq7 hrf0 hrf1 hrf7; omega) (by clear * - hrf1 hrf7; omega) (by clear * - hcq0 hcq1 hcq7 hrf1 hrf7; omega) (by clear * - hcq0 hcq1 hcq7 hrf1 hrf7; omega) (by clear * - hcq1 hrf7; omega) (by clear * - hcq0 hcq7 hrf1 hrf7; omega) (by clear * - hcq0 hcq7 hrf1 hrf7; omega) (by clear * - hcq0 hcq7 hrf0 hrf1 hrf7; omega) (by clear * - hcq0 hrf0 hrf7; omega) (by clear * - hcq0 hcq1 hrf0 hrf7; omega) (by clear * - hcq0 hcq1 hcq7 hrf7; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq7 hrf0 hrf1 hrf7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hrf0 hrf1 hrf7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hrf1 hrf7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hrf1 hrf7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hrf0 hrf1 hrf7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hrf1 hrf7; omega))
  have hlead : (xiQuarticChamberFace1810 A B C D E F G).natDegree =
      C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberFace1810_natDegree A B C D E F G hCne hDne
  rw [degreeZeroXiQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hxi; omega

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

set_option maxHeartbeats 64000000 in
/-- Refined leaf 1 of chamber `BCDEFG` / `CG·EE·CCC` dies on power system `S33`. -/
theorem quarticRefinedBCDEFG108L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG108L1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hApos hcq10 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * D.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4202 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3655 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4203 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3657 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0524 A.natDegree B.natDegree C.natDegree E.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4204 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4205 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3660 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq10 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4206 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4207 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3663 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4208 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3665 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0533 A.natDegree B.natDegree C.natDegree E.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4209 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4210 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3668 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq10 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4211 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4212 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3670 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4213 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3672 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0542 A.natDegree B.natDegree C.natDegree E.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4214 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4215 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3675 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3676 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4216 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3677 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq10 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0611 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq10 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4217 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3678 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4218 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3680 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0554 A.natDegree B.natDegree C.natDegree E.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4219 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4220 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3682 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0619 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4221 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3684 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hrf0 hcq0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3685 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf0 hcq0 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3686 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq10 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0624 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq0 hcq10 hcq1)
  have hr0 : (kappaQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest17810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq3; omega) (by clear * - hcq0 hcq3 hrf2 hcq10; omega) (by clear * - hcq1 hrf2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hcq10; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hcq10; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hcq10; omega)) (Or.inr (by clear * - hcq3; omega))
  have hct0 := kappaQuarticChamberFace17810_coeff_top_S33 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face17_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS33810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hApos hcq10 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4222 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4223 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4224 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4225 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4226 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq2 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4227 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4228 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4229 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq3 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4230 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4231 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4232 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4233 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq2 hcq0 hrf2 hcq10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_4234 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hrf2 hcq10 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4235 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hrf0 hcq0 hrf2 hcq10 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_4236 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq3 h hcq0 hrf2)
      · exact Or.inr (astra4u_Round4Package_nat_4237 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2)
      · exact Or.inr (astra4u_Round4Package_nat_4238 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4239 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4240 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq2 hcq0 hrf2 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_4241 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hrf2 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_4242 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hcq0 hrf2 hcq10 hcq1)
  have hr1 : (xiQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest11810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by clear * - hcq0 hcq1 hcq3 hcq10; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq3 hrf2; omega) (by clear * - hcq0 hcq1 hcq3 hrf2 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hrf2; omega) (by clear * - hcq0 hcq3 hcq10; omega) (by clear * - hcq0 hcq2 hcq10; omega) (by clear * - hcq0 hcq3 hrf2 hcq10; omega) (by clear * - hcq0 hcq2 hrf0 hrf2 hcq10; omega) (by clear * - hcq0 hcq1 hcq4 hcq10; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf2 hcq10; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf2 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf0 hrf2 hcq10; omega))
  have hct1 := xiQuarticChamberFace11810_coeff_top_S33 hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega)
  have hqq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : xiQuarticPowerInnerS33810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS33810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hBc hCc hEc hFc hGc

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
