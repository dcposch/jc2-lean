import Grok810ScaleZeroQuarticChamberPowerKillsPart25Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart26Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart27Scratch
import Grok810ScaleZeroQuarticChamberRests5Scratch

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
/-- Chamber `BDEG` / `BG·DD·DE·EE·BBB` dies on power system `S14` (carriers κ, ξ, π). -/
theorem quarticChamberBDEG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
  have hr0 : (kappaQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest13810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hFz (by clear * - hcq4; omega) hz0l hz0beta hz0delta (Or.inr (by clear * - hcq4; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq3 hcq4; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace13810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hFz (by clear * - hcq1 hcq3 hcq4; omega) (by clear * - hcq1 hcq3 hcq4; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4; omega)) hz1delta (Or.inr (by clear * - hcq1 hcq3 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4; omega))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S14 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1; omega
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  have hz2l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
  have hr2 : (piQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest11810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hCz hFz (by clear * - hcq4; omega) (by clear * - hcq4; omega) (by clear * - hcq3 hcq4; omega) (by clear * - hcq1 hcq3 hcq4; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4; omega)) (Or.inr (by clear * - hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4; omega))
  have hct2 := piQuarticChamberFace11810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1 hdp2; omega
  rw [degreeZeroPiQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS14810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hGc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
