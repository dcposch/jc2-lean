import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart16Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart17Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart18Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart19Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberRests6Scratch

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
/-- Refined leaf 1 of chamber `CDEFG` / `CG·DD·CCC` dies on the single-monomial `ξ` face. -/
theorem quarticRefinedCDEFG28L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedCDEFG28L1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4⟩ := hch
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < C.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hrf0 hrf1 hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3701 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3422 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3702 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf1 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3703 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3704 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3705 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3706 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf1 hrf0 hcq0 hcq1)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3707 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3429 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3708 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf1 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3709 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3710 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3711 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3712 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf1 hrf0 hcq0 hcq1)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3713 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 h hBn hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3714 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3715 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hrf1 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3716 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq5 hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3717 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3718 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 h hBn hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3719 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hrf1 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3720 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3721 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq5 hrf1 hcq0 hcq1)
  have hr0 : (xiQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberRest1810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz (by clear * - hrf1; omega) (by clear * - hcq0 hcq1 hrf0 hrf1; omega) (by clear * - hcq0 hrf0 hrf1; omega) (by clear * - hcq0 hcq1 hcq5 hrf1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hrf0 hrf1 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hrf0 hrf1; omega)) (Or.inr (by clear * - hcq0 hcq1 hrf0 hrf1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hrf0 hrf1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hrf0 hrf1; omega))
  have hlead : (xiQuarticChamberFace1810 A B C D E F G).natDegree =
      C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberFace1810_natDegree A B C D E F G hCne hDne
  rw [degreeZeroXiQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hxi; omega

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
/-- Refined leaf 2 of chamber `CDEFG` / `CG·DD·CCC` dies on power system `S34`. -/
theorem quarticRefinedCDEFG28L2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedCDEFG28L2810 A B C D E F G)
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
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10⟩ := hch
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq5 hrf0 hrf10 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3722 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3723 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3724 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3725 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3726 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hAB h hBn hrf0 hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3727 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3728 A.natDegree C.natDegree D.natDegree F.natDegree h hrf10)
      · exact Or.inr (astra4u_Round4Package_nat_3729 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3730 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf10 hrf0 hcq0 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3731 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3732 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3733 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3734 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3735 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hAB h hBn hrf0 hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3736 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3737 A.natDegree C.natDegree D.natDegree F.natDegree h hrf10)
      · exact Or.inr (astra4u_Round4Package_nat_3738 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3739 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf10 hrf0 hcq0 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3740 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3741 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3742 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hcq2 hBn hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3743 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 hAB h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3744 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3745 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3746 A.natDegree C.natDegree D.natDegree F.natDegree h hrf10)
      · exact Or.inr (astra4u_Round4Package_nat_3747 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3748 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3749 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3750 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hBn hcq0 hcq4 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3751 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf10 hrf0 hcq0 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3752 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf10 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3753 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf10 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3754 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3755 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3756 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3757 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3758 A.natDegree C.natDegree D.natDegree F.natDegree h hrf10)
      · exact Or.inr (astra4u_Round4Package_nat_3759 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3760 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hrf0 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3761 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3762 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hBn hcq0 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3763 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3764 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3765 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
  have hz0theta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3766 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hrf10 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3767 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3768 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hBn hrf10 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3769 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3770 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hrf0 hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3771 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3772 A.natDegree C.natDegree D.natDegree F.natDegree h hrf10)
    · exact Or.inr (astra4u_Round4Package_nat_3773 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq5 hBn hcq0 hcq4 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3774 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hrf0 hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3775 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3776 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq5 hBn hcq0 hcq4 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3777 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3778 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq5 hAB hBn hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_3779 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
  have hr0 : (kappaQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest14810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hdp0 hrf10; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hdp0 hrf10; omega)) hz0zeta hz0theta
  have hct0 := kappaQuarticChamberFace14810_coeff_top_S34 hCne hDne hEne hFne (A := A) (B := B) (G := G) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0; omega)
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
  have hz1l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_3780 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3781 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3782 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3783 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3784 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3785 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3786 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_3787 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3788 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3789 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3790 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3791 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3792 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3793 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
  have hz1delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_3794 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3795 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3796 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3797 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3798 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3799 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3800 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hrf10 hcq0 hcq1)
  have hr1 : (muQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest19810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz (by clear * - hcq0 hcq1 hcq2 hrf10; omega) (by clear * - hcq0 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega))
  have hct1 := muQuarticChamberFace19810_coeff_top_S34 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1; omega)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3801 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3802 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3803 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3804 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3805 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3806 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3807 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hrf0 hcq0 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3808 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3809 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3810 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3811 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3812 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3813 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3814 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hrf10 hrf0 hcq0 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3815 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3816 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3817 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3818 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3819 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3820 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3821 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3822 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq2 hBn hrf10 hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3823 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
  have hz2zeta : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbzeta with h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3824 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3825 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3826 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3827 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3828 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3829 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3830 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3831 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hAB hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3832 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3833 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hrf10 hcq0 hcq1)
  have hr2 : (xiQuarticChamberRest23810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest23810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hBz (by clear * - hrf10; omega) (by clear * - hcq0 hcq1 hcq2 hrf10; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf0 hrf10; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega)) hz2zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf0 hrf10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega))
  have hct2 := xiQuarticChamberFace23810_coeff_top_S34 hAne hCne hDne hEne hFne hGne (B := B) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1 hdp2; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1 hdp2; omega)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_3780 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3834 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3835 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3836 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3837 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3838 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3839 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hrf0 hcq0 hcq1)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_3787 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3840 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3841 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3842 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3843 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3844 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3845 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hrf0 hcq0 hcq1)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_3794 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 hBn hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3846 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_3847 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3848 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3849 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_3850 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hrf10 hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3851 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq2 hrf10 hcq0 hcq1)
  have hr3 : (piQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest13810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hBz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hrf10; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hrf10; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf10; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf10; omega))
  have hct3 := piQuarticChamberFace13810_coeff_top_S34 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1 hdp2 hdp3; omega)
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
/-- Refined leaf 0 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` dies on power system `S29`. -/
theorem quarticRefinedBCDEFG7L0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG7L0810 A B C D E F G)
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
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16, hrf17, hrf18, hrf19, hrf20, hrf21, hrf22, hrf23, hrf24, hrf25⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3303 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3852 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3305 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3306 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3853 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3308 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3309 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3310 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3854 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3312 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3855 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3314 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3315 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3856 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3317 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3318 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3319 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3857 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3321 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3858 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3322 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3323 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3859 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3324 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3325 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3326 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3860 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3328 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3329 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 hcq3 h hrf19)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3861 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3331 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3862 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3333 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3334 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3863 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3336 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3337 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3338 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3864 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3339 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3340 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 hcq3 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3341 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 hcq3 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3342 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3343 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3344 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq0 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3865 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq0 hrf18 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3346 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3347 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3866 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq1 hcq0 hrf18 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3350 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq1 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3351 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3867 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq0 hrf18 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3353 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3354 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3355 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3356 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
    · exact Or.inr (astra4u_Round4Package_nat_3357 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3 hrf19)
  have hr0 : (kappaQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest11810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq7 hrf19; omega) (by clear * - hcq0 hcq3 hcq7 hrf18; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf19; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq3 hcq7 hrf18; omega)) hz0zeta (Or.inr (by clear * - hcq3 hcq7 hrf19; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace11810_coeff_top_S29 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3358 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3359 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3868 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3360 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3361 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3362 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3869 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3364 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3365 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3870 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3366 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 hcq1 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3367 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3368 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3871 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3370 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3371 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3872 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3372 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3373 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3374 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3375 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3376 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3377 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
  have hr1 : (muQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest16810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by clear * - hcq1 hcq3 hcq7 hrf19; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7 hrf18 hrf19; omega) (by clear * - hcq7 hrf19; omega) (by clear * - hcq1 hcq3 hcq7 hrf19; omega) (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) (Or.inr (by clear * - hcq3 hcq7 hrf19; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf19; omega))
  have hct1 := muQuarticChamberFace16810_coeff_top_S29 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3378 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3379 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3873 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3381 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3382 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3383 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3874 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3385 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3386 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3875 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3388 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 hcq1 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3389 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3390 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3876 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3392 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3393 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3877 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3395 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3396 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3397 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3398 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3399 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3878 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq1 hcq0 hrf18 hrf19)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by clear * - hcq1 hcq3 hrf19; omega) (by clear * - hcq0 hcq1 hrf18; omega) (by clear * - hcq1 hcq3 hcq7 hrf19; omega) (by clear * - hcq1 hcq3 hrf19; omega) (by clear * - hcq0 hcq1 hrf19; omega) (by clear * - hrf19; omega) (by clear * - hcq0 hcq1 hcq7 hrf18 hrf19; omega) (by clear * - hcq0 hcq1 hrf18; omega) (by clear * - hcq7 hrf19; omega) (by clear * - hcq1 hcq3 hrf18; omega) (by clear * - hcq1 hcq3 hrf19; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf19; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf19; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf19; omega))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S29 hAne hBne hCne hDne hFne (E := E) (G := G) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3401 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3402 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3879 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3403 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3404 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3405 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3880 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3407 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3408 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3881 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3409 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 hcq1 h hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3410 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3411 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3882 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq3 h hcq1 hcq0 hrf18 hrf19)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_3413 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3414 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3883 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0 hrf18 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3415 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq3 hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3416 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3417 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3418 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
      · exact Or.inr (astra4u_Round4Package_nat_3419 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq3 h hcq1 hrf19)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_3884 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq1 hcq0 hrf18 hrf19)
  have hr3 : (piQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest9810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by clear * - hcq7 hrf19; omega) (by clear * - hcq1 hcq3 hcq7 hrf19; omega) (by clear * - hcq0 hcq3 hcq7 hrf18; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq7 hrf19; omega) (by clear * - hcq0 hcq1 hcq7 hrf18 hrf19; omega) (by clear * - hcq7 hrf19; omega) (by clear * - hcq1 hcq7 hrf19; omega) (by clear * - hcq0 hcq3 hcq7 hrf19; omega) (by clear * - hcq0 hcq3 hcq7 hrf18 hrf19; omega) (by clear * - hcq1 hcq3 hcq7 hrf19; omega) (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18; omega) (by clear * - hcq0 hcq3 hcq7 hrf18 hrf19; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hrf18 hrf19; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hrf19; omega))
  have hct3 := piQuarticChamberFace9810_coeff_top_S29 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hrf22 hrf23 hrf24 hrf25 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2 hdp3; omega)
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
