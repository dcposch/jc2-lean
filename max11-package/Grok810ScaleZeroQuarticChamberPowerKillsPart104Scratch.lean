import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch

/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `DD·DE·EE·BBB·BBC·BCC·CCC` dies on power system `S06` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDE9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE9810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq2 hcq3 hcq6 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
  have hr0 : (kappaQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest8810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz hGz (by clear * - hcq0 hcq2 hcq7; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace8810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face8_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq2 hcq3 hcq6 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hr1 : (muQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest13810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz hGz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hct1 := muQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq2 hcq3 hcq6 hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hr2 : (xiQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest13810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hFz hGz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq2 hcq3 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq2 hcq3 hcq7; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7; omega))
  have hct2 := xiQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2; omega
  rw [degreeZeroXiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq2 hcq3 hcq6 hzero; omega)
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hr3 : (piQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hFz hGz (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq2 hcq3 hcq7; omega) (by clear * - hcq2 hcq3 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq2 hcq3 hcq7; omega) (by clear * - hcq2 hcq7; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega))
  have hct3 := piQuarticChamberFace6810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2 hdp3; omega)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1 hdp2 hdp3; omega
  rw [degreeZeroPiQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS06810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `DD·DE·EE·BBB·BBC·BCC·CCC` dies on power system `S06` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEF46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF46810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq2 hcq3 hcq6 hcq8 hApos hcq11 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq2 hcq6 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
    · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
  have hr0 : (kappaQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest8810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq2 hcq3 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq12; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq12; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace8810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face8_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq2 hcq3 hcq6 hcq8 hApos hcq11 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hr1 : (muQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest13810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by clear * - hcq0 hcq3 hcq12; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq3 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega))
  have hct1 := muQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq2 hcq3 hcq6 hcq8 hApos hcq11 hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hr2 : (xiQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest13810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hGz (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq0 hcq2 hcq6 hcq12; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq12; omega))
  have hct2 := xiQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2; omega
  rw [degreeZeroXiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq2 hcq3 hcq6 hcq8 hApos hcq11 hzero; omega)
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq12; omega)
  have hr3 : (piQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hGz (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq2 hcq3 hcq6; omega) (by clear * - hcq0 hcq2 hcq6 hcq12; omega) (by clear * - hcq2 hcq3 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq2 hcq6; omega) (by clear * - hcq2 hcq6 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega) (by clear * - hcq2 hcq12; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq12; omega))
  have hct3 := piQuarticChamberFace6810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2 hdp3; omega)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2 hdp3; omega
  rw [degreeZeroPiQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS06810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `DD·DE·EE·BBB·BBC·BCC·CCC` dies on power system `S06` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEG46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG46810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq2 hcq3 hcq6 hcq11 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
  have hr0 : (kappaQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest8810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq3 hcq7; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hcq12; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq2 hcq12; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace8810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face8_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq2 hcq3 hcq6 hcq11 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hr1 : (muQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest13810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by clear * - hcq0 hcq3 hcq12; omega) (by clear * - hcq3 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq3 hcq7; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7 hcq12; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq3 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq12; omega))
  have hct1 := muQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq2 hcq3 hcq6 hcq11 hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hr2 : (xiQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest13810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hFz (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq0 hcq3 hcq7 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq3 hcq7; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq12; omega))
  have hct2 := xiQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2; omega
  rw [degreeZeroXiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq2 hcq3 hcq6 hcq11 hzero; omega)
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7 hcq12; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12; omega)
  have hr3 : (piQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hFz (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq2 hcq3 hcq12; omega) (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq12; omega) (by clear * - hcq0 hcq2 hcq3 hcq7 hcq12; omega) (by clear * - hcq2 hcq3 hcq7; omega) (by clear * - hcq2 hcq12; omega) (by clear * - hcq3 hcq7; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq12; omega))
  have hct3 := piQuarticChamberFace6810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega
  rw [degreeZeroPiQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS06810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
