import Grok810ScaleZeroQuarticChamberRests6Scratch
import Grok810ScaleZeroQuarticPowerCertificatesScratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart11Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart12Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart13Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart14Scratch

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
/-- Refined leaf 1 of chamber `BCDEFG` / `CG·DD·CCC` dies on power system `S30`. -/
theorem quarticRefinedBCDEFG102L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L1810 A B C D E F G)
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
    clear * - hApos hz0; omega
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hrf0 hrf5 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * D.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hrf5; omega)
  have hr0 : (kappaQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest17810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq3; omega) (by clear * - hcq3 hrf5; omega) (by clear * - hcq1 hrf2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf5; omega)) hz0delta (Or.inr (by clear * - hcq3 hrf5; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq3; omega))
  have hct0 := kappaQuarticChamberFace17810_coeff_top_S30 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face17_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hrf0 hrf5 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf2 hrf5; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
  have hr1 : (muQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest19810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq2 hrf5; omega) (by clear * - hcq0 hcq3 hrf2; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega))
  have hct1 := muQuarticChamberFace19810_coeff_top_S30 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega)
  have hqq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : muQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hdp2 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq6 hcq7 hrf0 hrf5 hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq3 hrf2; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq3 hrf5; omega) (by clear * - hcq0 hcq2 hrf5; omega) (by clear * - hcq0 hcq2 hrf0 hrf2 hrf5; omega) (by clear * - hcq0 hrf2; omega) (by clear * - hrf5; omega) (by clear * - hcq0 hcq1 hrf2; omega) (by clear * - hcq0 hcq1 hcq2 hrf0 hrf5; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S30 hAne hBne hCne hDne hFne (E := E) (G := G) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega)
  have hqq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega
  rw [degreeZeroXiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hqq2
  have hin2 : xiQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hqq2
  have hdp3 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hrf0 hrf5 hzero; omega)
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf2 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)
  have hr3 : (piQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest13810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq3 hrf2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf2 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq3 hrf5; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq3 hrf5; omega) (by clear * - hcq0 hcq2 hcq3 hrf2 hrf5; omega) (by clear * - hcq0 hcq2 hrf5; omega) (by clear * - hcq0 hcq3 hrf2; omega) (by clear * - hcq0 hcq2 hrf0 hrf2 hrf5; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf2 hrf5; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf2 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf0 hrf2 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf5; omega))
  have hct3 := piQuarticChamberFace13810_coeff_top_S30 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega)
  have hqq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hrf26 hrf27 hrf28 hrf29 hrf30 hrf31 hrf32 hrf33 hrf34 hrf35 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega
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
