import Grok810ScaleZeroQuarticChamberPowerKillsPart32Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart33Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart34Scratch
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
/-- Chamber `BCEFG` / `BF·BG·CF·CG` dies on power system `S16` (carriers κ, μ, π). -/
theorem quarticChamberBCEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq6 hcq9 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq6 hcq10; omega)
  have hr0 : (kappaQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest16810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq10; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq10; omega))
  have hct0 := kappaQuarticChamberFace16810_coeff_top_S16 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + G.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq6 hcq9 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq6 hcq10; omega)
  have hr1 : (muQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest20810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hcq10; omega) (by clear * - hcq1 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq5 hcq10; omega) (by clear * - hcq1 hcq10; omega) (by clear * - hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq10; omega)) hz1delta (Or.inr (by clear * - hcq1 hcq3 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq10; omega))
  have hct1 := muQuarticChamberFace20810_coeff_top_S16 hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face20_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq6 hcq9 hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq10; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq10; omega)
  have hr2 : (piQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest14810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz (by clear * - hcq1 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq1 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq1 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq5 hcq10; omega) (by clear * - hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq5 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq3 hcq10; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq6 hcq10; omega)) hz2delta (Or.inr (by clear * - hcq1 hcq3 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq10; omega))
  have hct2 := piQuarticChamberFace14810_coeff_top_S16 hAne hFne hGne (B := B) (C := C) (D := D) (E := E) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega
  rw [degreeZeroPiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS16810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hAc hBc hCc hFc hGc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
