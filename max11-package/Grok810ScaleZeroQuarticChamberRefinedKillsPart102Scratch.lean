import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart15Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart16Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart17Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart18Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberRests6Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch

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
/-- Refined leaf 0 of chamber `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` dies on power system `S29`. -/
theorem quarticRefinedBCDFG7L0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDFG7L0810 A B C D E F G)
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
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16, hrf17⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hcell
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3303 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3304 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq3 hAE h hEn hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3305 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3306 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3307 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq3 hAE h hcq1 hEn hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3308 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3309 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3310 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3311 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf13)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3312 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3313 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq3 hAE h hEn hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3314 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3315 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3316 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq3 hAE h hcq1 hEn hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3317 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3318 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3319 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3320 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf13)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3321 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0258 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3322 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3323 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0260 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3324 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3325 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3326 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3327 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq3 hAE h hEn hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3328 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3329 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 hcq3 h hrf13)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3330 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3331 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3332 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq3 h hEn hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3333 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3334 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3335 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq3 h hcq1 hEn hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3336 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3337 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3338 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0271 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3339 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3340 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 hcq3 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3341 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 hcq3 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3342 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3343 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3344 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq0 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3345 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq7 hEn hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3346 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3347 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3348 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq7 hcq3 hcq1 hEn hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3350 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq1 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3351 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3352 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq7 hcq3 hEn hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3353 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3354 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3355 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3356 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
    · exact Or.inr (astra4u_Round4Package_nat_3357 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3 hrf13)
  have hr0 : (kappaQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest11810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by clear * - hcq7 hrf13; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) hz0delta (Or.inr (by clear * - hcq7 hrf13; omega)) hz0zeta (Or.inr (by clear * - hcq3 hcq7 hrf13; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace11810_coeff_top_S29 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3358 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3359 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0291 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hAE h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3360 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3361 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3362 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3363 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf13)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3364 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3365 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0298 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hAE h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3366 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 hcq1 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3367 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3368 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3369 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3370 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3371 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0305 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3372 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3373 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3374 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3375 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3376 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3377 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
  have hr1 : (muQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest16810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by clear * - hcq1 hcq3 hcq7 hrf13; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq7 hrf13; omega) (by clear * - hcq1 hcq3 hcq7 hrf13; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf13; omega)) hz1delta (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega))
  have hct1 := muQuarticChamberFace16810_coeff_top_S29 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega)
  have hqq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : muQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hdp2 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3378 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3379 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3380 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hAE h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3381 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3382 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3383 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3384 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf13)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3385 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3386 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3387 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hAE h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3388 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 hcq1 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3389 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3390 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3391 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3392 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3393 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3394 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3395 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3396 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3397 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3398 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3399 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3400 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz (by clear * - hcq1 hcq3 hrf13; omega) (by clear * - hcq1 hcq3 hcq7 hrf13; omega) (by clear * - hcq1 hcq3 hrf13; omega) (by clear * - hcq0 hcq1 hrf13; omega) (by clear * - hrf13; omega) (by clear * - hcq7 hrf13; omega) (by clear * - hcq1 hcq3 hrf13; omega) hz2l hz2beta (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S29 hAne hBne hCne hDne hFne (E := E) (G := G) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2; omega)
  have hqq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hqq2
  have hin2 : xiQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hqq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3401 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3402 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0314 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hAE h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3403 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3404 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3405 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3406 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf13)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3407 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3408 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0321 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hAE h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3409 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 hcq1 h hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3410 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3411 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3412 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3413 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3414 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_0328 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq1 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3415 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3416 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3417 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3418 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
      · exact Or.inr (astra4u_Round4Package_nat_3419 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf13)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3420 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf13)
  have hr3 : (piQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hEz (by clear * - hcq7 hrf13; omega) (by clear * - hcq1 hcq3 hcq7 hrf13; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq7 hrf13; omega) (by clear * - hcq7 hrf13; omega) (by clear * - hcq1 hcq7 hrf13; omega) (by clear * - hcq0 hcq3 hcq7 hrf13; omega) (by clear * - hcq1 hcq3 hcq7 hrf13; omega) hz3l hz3beta (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) hz3delta (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf13; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf13; omega))
  have hct3 := piQuarticChamberFace9810_coeff_top_S29 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega)
  have hqq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hqq3
  have hin3 : piQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hqq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS29810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hBc hCc hDc hFc hGc

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
/-- Refined leaf 1 of chamber `BCDFG` / `CG·DD·CCC` dies on the single-monomial `ξ` face. -/
theorem quarticRefinedBCDFG54L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDFG54L1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < C.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq3 hcq6 hrf0 hrf4 hApos hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3421 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3422 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3423 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq6 hAE h hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3424 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3425 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3426 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3427 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3428 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3429 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3430 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3431 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 hrf4 h hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3432 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3433 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3434 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hrf4 hrf0 hcq0 hcq1)
  have hr0 : (xiQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberRest1810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega) (by clear * - hcq1 hrf0 hrf4; omega) (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega) (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega) (by clear * - hrf4; omega) (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega) (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega) (by clear * - hcq0 hcq1 hcq6 hrf4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hrf0 hrf4; omega))
  have hlead : (xiQuarticChamberFace1810 A B C D E F G).natDegree =
      C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberFace1810_natDegree A B C D E F G hCne hDne
  rw [degreeZeroXiQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hxi; omega

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
/-- Refined leaf 2 of chamber `BCDFG` / `CG·DD·CCC` dies on power system `S30`. -/
theorem quarticRefinedBCDFG54L2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDFG54L2810 A B C D E F G)
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
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16, hrf17, hrf18, hrf19⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq3 hcq6 hrf0 hrf16 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * D.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3435 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3436 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hAE h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3437 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3438 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3439 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hAE h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3440 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3441 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3442 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3443 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3444 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3445 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hAE h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3446 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3447 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3448 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hAE h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3449 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3450 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3451 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3452 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3453 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3454 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hAE h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3455 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3456 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3457 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hAE h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3458 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3459 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3460 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3461 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3462 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3463 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3464 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3465 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3466 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3467 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3468 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3469 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3470 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3471 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf0 hrf16 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3472 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3473 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3474 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3475 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq4 hcq2 h hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3476 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3477 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3478 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf16 hcq0 hcq1)
  have hr0 : (kappaQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest17810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by clear * - hcq3; omega) (by clear * - hcq1 hcq2 hrf16; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf16; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq2 hrf16; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq3; omega))
  have hct0 := kappaQuarticChamberFace17810_coeff_top_S30 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face17_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3195 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3196 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3479 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3480 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3481 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3482 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3483 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3202 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3203 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3484 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3485 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3486 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3487 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3488 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3209 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3210 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3489 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3490 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3491 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3492 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3493 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf0 hrf16 hcq0 hcq1)
  have hr1 : (muQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest19810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq2 hcq3 hrf16; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hrf16; omega) (by clear * - hcq0 hcq1 hcq2 hrf0 hrf16; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hrf16; omega))
  have hct1 := muQuarticChamberFace19810_coeff_top_S30 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega)
  have hqq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : muQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hdp2 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3494 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3495 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3496 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq2 hrf0 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3497 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3498 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3499 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3500 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3501 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3502 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3503 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3504 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3505 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3506 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3507 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3508 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3509 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3510 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 h hrf0 hcq0 hcq5 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3511 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3512 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3513 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3514 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf0 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3515 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3516 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz (by clear * - hcq0 hcq2 hcq3 hrf16; omega) (by clear * - hcq0 hcq1 hcq2 hrf16; omega) (by clear * - hcq0 hcq2 hrf16; omega) (by clear * - hcq0 hcq1 hcq2 hrf16; omega) (by clear * - hcq0 hcq1 hcq2 hrf0 hrf16; omega) (by clear * - hcq1 hrf0 hrf16; omega) (by clear * - hcq0 hcq1 hcq2 hrf0 hrf16; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hrf0 hrf16; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf16; omega))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S30 hAne hBne hCne hDne hFne (E := E) (G := G) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2; omega)
  have hqq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hqq2
  have hin2 : xiQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hqq2
  have hdp3 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3239 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3240 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3517 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3480 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3518 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3519 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3520 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3245 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3246 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3521 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3485 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3522 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3523 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3524 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3251 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3252 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3525 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3490 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq2 hrf16 hcq0 hEn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3526 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3527 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf16 hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3528 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq2 hrf0 hrf16 hcq0 hcq1)
  have hr3 : (piQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest13810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hEz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq2 hcq3 hrf16; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq2 hcq3 hrf16; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hrf16; omega) (by clear * - hcq0 hcq1 hcq2 hrf16; omega) (by clear * - hcq0 hcq2 hrf16; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq2 hrf16; omega) (by clear * - hcq0 hcq1 hcq2 hrf0 hrf16; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hrf16; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf16; omega))
  have hct3 := piQuarticChamberFace13810_coeff_top_S30 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2 hdp3; omega)
  have hqq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hqq3
  have hin3 : piQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hqq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS30810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hBc hCc hDc hFc hGc

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
/-- Refined leaf 0 of chamber `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` dies on power system `S32`. -/
theorem quarticRefinedBCEFG7L0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCEFG7L0810 A B C D E F G)
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
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16⟩ := hch
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hcell
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3529 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3530 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3531 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3532 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3533 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3534 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3535 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3536 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3537 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3538 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3539 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3540 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3541 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3542 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3543 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3544 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3545 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3546 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3547 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3548 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3549 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3550 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3551 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3552 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3553 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3554 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3555 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3556 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3557 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3558 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3559 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3560 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3561 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3562 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3563 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3564 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3565 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3566 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3567 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3568 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3569 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_3570 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3571 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3572 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3573 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_3574 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3575 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq0 h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_3576 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3577 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3578 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_3579 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_3580 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3581 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3582 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_3583 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3584 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3585 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_3586 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq0 hDn)
  have hr0 : (kappaQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest11810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq3 hcq7 hrf12; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace11810_coeff_top_S32 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3587 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3588 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3589 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 hAD h hcq1 hcq0 hDn hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3590 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3591 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3592 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3593 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3594 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3595 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3596 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hAD hcq1 hcq0 hDn hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3597 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq1 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_3598 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3599 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3600 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3601 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3602 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3603 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq0 hDn hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3604 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3605 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3606 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3607 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3608 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3609 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
  have hr1 : (muQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest16810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega) (by clear * - hcq0 hcq1 hcq7 hrf12; omega) (by clear * - hcq1 hcq3 hcq7; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega))
  have hct1 := muQuarticChamberFace16810_coeff_top_S32 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
  have hqq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : muQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3610 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3611 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hrf12 hcq3 h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_3612 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3613 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3614 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3615 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3616 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3617 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3618 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hrf12 hcq3 h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_3619 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3620 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3621 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3622 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3623 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
  have hz2delta : delta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3624 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hrf12 hcq3 hcq1 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_3625 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hrf12 hcq3 h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_3626 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3627 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3628 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3629 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3630 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq1 hcq0 h)
  have hr2 : (xiQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest16810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz (by clear * - hcq0 hcq3 hrf12; omega) (by clear * - hcq0 hcq1 hcq3 hrf12; omega) (by clear * - hcq0 hrf12; omega) (by clear * - hcq0 hcq1 hrf12; omega) (by clear * - hcq0 hcq3 hrf12; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7 hrf12; omega))
  have hct2 := xiQuarticChamberFace16810_coeff_top_S32 hAne hBne hCne hEne hGne (D := D) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega)
  have hqq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hqq2
  have hin2 : xiQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hqq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3631 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3632 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3633 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 hAD h hcq1 hcq0 hDn hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3634 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3635 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hAD h hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3636 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3637 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3638 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3639 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3640 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hAD hcq1 hcq0 hDn hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3641 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 hcq1 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_3642 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3643 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3644 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3645 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3646 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3647 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq0 hDn hcq9 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_3648 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3649 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hAD hcq1 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_3650 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3651 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3652 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hrf12 hcq3 h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3653 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hrf12 hcq3 hcq1 hcq0)
  have hr3 : (piQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hDz (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega) (by clear * - hcq0 hcq7 hrf12; omega) (by clear * - hcq0 hcq1 hcq7 hrf12; omega) (by clear * - hcq0 hcq3 hcq7 hrf12; omega) (by clear * - hcq1 hcq3 hcq7; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf12; omega))
  have hct3 := piQuarticChamberFace9810_coeff_top_S32 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2 hdp3; omega)
  have hqq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hqq3
  have hin3 : piQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hqq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS32810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hBc hCc hEc hFc hGc

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
/-- Refined leaf 1 of chamber `BCEFG` / `CG·EE·CCC` dies on power system `S33`. -/
theorem quarticRefinedBCEFG54L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCEFG54L1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7⟩ := hch
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq3 hcq6 hrf0 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3654 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3655 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3656 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hAD h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3657 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0524 A.natDegree B.natDegree C.natDegree E.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_3658 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hAD h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3659 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3660 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq6 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3661 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hcq6 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3662 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3663 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3664 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hAD hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3665 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0533 A.natDegree B.natDegree C.natDegree E.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_3666 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3667 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3668 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq6 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0600 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3669 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3670 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3671 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hAD hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3672 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0542 A.natDegree B.natDegree C.natDegree E.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_3673 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3674 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3675 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3676 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0609 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hAD hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3677 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq6 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0611 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0612 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_3678 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hrf0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3679 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3680 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0554 A.natDegree B.natDegree C.natDegree E.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_3681 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0617 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3682 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0619 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3683 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3684 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hrf0 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3685 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hrf0 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3686 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf0 hcq0 hcq6 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0624 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1)
  have hr0 : (kappaQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest17810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq6; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq3; omega))
  have hct0 := kappaQuarticChamberFace17810_coeff_top_S33 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq3 hcq6 hrf0 hApos hzero; omega)
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3687 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3688 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3689 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3690 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3691 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq2 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3692 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3693 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf0 hcq0 hcq6 hcq1)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3694 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3695 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_3696 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hrf0 hcq0 hDn hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3697 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3698 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq2 hcq0 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3699 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq6 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3700 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hrf0 hcq0 hcq6 hcq1)
  have hr1 : (xiQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest11810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hcq0 hcq1 hcq3 hcq6; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hcq6; omega) (by clear * - hcq0 hcq3 hcq6; omega) (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq1 hcq4 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega))
  have hct1 := xiQuarticChamberFace11810_coeff_top_S33 hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
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
