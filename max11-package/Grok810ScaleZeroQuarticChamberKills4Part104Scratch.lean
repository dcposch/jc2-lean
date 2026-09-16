import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart00Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberInnerScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests4Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `CG·CCC`: the faces of μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDFG52810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG52810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq6 hcq8 hcq9 hApos hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0950 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0951 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0952 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0656 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0953 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq3 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0954 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0955 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq9 hcq0)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0898 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq2 hcq4 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0660 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0661 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0576 A.natDegree B.natDegree C.natDegree G.natDegree h hcq2 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0956 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9 hcq0)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq2 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0900 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq2 hcq4 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0663 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0664 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0583 A.natDegree B.natDegree C.natDegree G.natDegree h hcq2 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0957 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq2 hcq4 hcq1 hcq9 hcq0)
  have hr0 : (muQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest7810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq2 hcq4 hcq9; omega) (by clear * - hcq0 hcq3 hcq4 hcq9; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) hz0delta (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace7810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq6 hcq8 hcq9 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ 5 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ B.natDegree + 3 * C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 4 * C.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0958 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0959 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0960 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0656 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0961 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq3 hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0962 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0963 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq1 hcq9 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + F.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * D.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0671 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0672 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0964 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0660 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0673 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0674 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq9 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0965 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq1 hcq9 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0676 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq2 hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0677 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0966 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq4 hcq3 hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0663 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0678 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0679 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq9 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0967 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq2 hcq4 hcq1 hcq9 hcq0)
  have hr1 : (piQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest1810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by clear * - hcq2; omega) (by clear * - hcq2 hcq4 hcq9; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq2 hcq4 hcq9; omega) (by clear * - hcq2 hcq4 hcq9; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2 hcq4 hcq9; omega) (by clear * - hcq0 hcq3 hcq4 hcq9; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace1810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticChamberInnerSystem5810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0157 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0407 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0968 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAB h hcq0 hcq14 hcq5 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0159 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0409 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0476 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAB h hcq0 hcq14 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0161 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0410 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq14)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0162 A.natDegree B.natDegree D.natDegree G.natDegree hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0411 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0039 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0146 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0163 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0412 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq4; omega) (by clear * - hcq5; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq14 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0969 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAB h hcq0 hcq14 hcq5 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq14 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0414 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq14 hcq5)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0136 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq14 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0076 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0155 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0156 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq4; omega) (by clear * - hcq0 hcq7; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq5 hcq7 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face3_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticChamberInnerSystem0810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·CF·BBB·BBC·BCC·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG17810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
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
      · exact Or.inr (astra4u_Round4Package_nat_0970 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0416 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0417 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 hAD h hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0418 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0419 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 hAD h hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0420 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0249 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0971 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq1 h hcq0 hcq6 hcq10)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0972 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0423 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0424 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 h hAD hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0425 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0973 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0427 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0255 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0974 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq1 h hcq0 hcq6 hcq10)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0975 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAD hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0430 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0976 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0432 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0977 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0978 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0261 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0435 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0436 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0264 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0437 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq0 hcq10)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0979 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0439 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0440 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0268 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0441 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0980 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0443 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0270 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0444 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0981 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0273 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0274 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0275 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0276 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0982 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq6 hDn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0446 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq7 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0983 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 h hDn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0280 A.natDegree B.natDegree F.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0447 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq7 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0984 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq6 hDn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0985 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hDn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0449 A.natDegree B.natDegree E.natDegree F.natDegree h hcq7 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0986 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq6 hDn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0285 A.natDegree B.natDegree F.natDegree h hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0287 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0987 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq6 hDn hcq10)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq0 hcq1 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0923 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0290 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0452 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 hAD h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0292 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0453 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0294 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0988 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq1 h hcq0 hcq6 hcq10)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0925 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0297 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0456 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hAD hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0299 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0457 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0301 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0458 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq0 hcq10)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0926 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0304 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0460 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0306 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0989 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0308 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0309 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0310 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0462 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
  have hr1 : (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq7 hcq10; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq7; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace9810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0927 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0313 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0464 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 hAD h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0315 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0465 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0317 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0990 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 hcq1 h hcq0 hcq6 hcq10)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0929 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0320 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0468 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hAD hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0322 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0469 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0324 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0470 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 hcq1 h hcq0 hcq10)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0930 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0327 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0472 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0329 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0991 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hDn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0331 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0332 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0333 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0474 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq1 hcq0 hcq10)
  have hr2 : (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest2000810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq7 hcq10; omega) (by clear * - hcq1 hcq7 hcq10; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct2 := piQuarticChamberFace2000810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face2000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact quarticNoTargetInner_ABCF_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff hin0 hin1 hin2 hAc hBc hCc hFc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEFG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG27810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
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
    exact (Nat.ne_of_gt hApos) hz0
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
      · exact Or.inr (astra4u_Round4Package_nat_0806 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0807 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0808 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0478 A.natDegree B.natDegree C.natDegree E.natDegree hcq3 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0173 A.natDegree B.natDegree D.natDegree G.natDegree hcq9 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0479 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0348 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0992 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq6 hcq9 h hcq8 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0811 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0812 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0813 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0482 A.natDegree B.natDegree C.natDegree E.natDegree hcq3 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0814 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0484 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0355 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0485 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 hcq6 hcq9 h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0817 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0818 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0819 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0489 A.natDegree B.natDegree C.natDegree E.natDegree hcq3 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0820 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0491 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0362 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0194 A.natDegree B.natDegree E.natDegree G.natDegree hcq6 hcq9 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0492 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq9 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0493 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq3 hcq6 hcq9 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0198 A.natDegree B.natDegree D.natDegree G.natDegree hcq9 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0823 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq4 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0200 A.natDegree B.natDegree D.natDegree G.natDegree h hcq9 hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0713 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0495 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq3 h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0824 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0497 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0371 A.natDegree B.natDegree C.natDegree hApos hcq3 h)
      · exact Or.inr (astra4u_Round4Package_nat_0206 A.natDegree B.natDegree E.natDegree G.natDegree hcq6 hcq9 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0993 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq9 h hDn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq9 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0716 A.natDegree B.natDegree F.natDegree G.natDegree hcq9 h hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0375 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0376 A.natDegree B.natDegree C.natDegree hApos h hcq3)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0211 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0827 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq4 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0717 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0501 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq3 hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0828 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq9 hDn hcq8 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0503 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq9 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0382 A.natDegree B.natDegree C.natDegree hApos h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0217 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0504 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq9 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0386 A.natDegree B.natDegree C.natDegree G.natDegree h hcq3 hcq9 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0831 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq9 hDn hcq8 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq3; omega) (by clear * - hcq0 hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq3; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0994 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq6 hcq9 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0995 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq6 hcq9 h hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0996 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq6 hcq9 hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0997 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq6 hcq9 hcq1 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0998 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq6 hcq9 hcq8 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0999 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq6 hcq9 h hcq5 hcq8 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1000 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos hcq3 h hcq4 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1001 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq6 h hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1002 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq6 h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1003 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq6 hcq1 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1004 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq6 hcq9 hcq8 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1005 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos hcq3 hcq9 h hcq4 hcq1 hcq2 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0944 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0945 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 h hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1006 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos hcq3 hcq4 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0947 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0948 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hApos h hcq3 hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1007 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq3 hcq4 hcq1 hcq2 hcq0)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hcq3; omega) (by clear * - hcq0 hcq3 hcq9; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq8; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq3 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face3_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticChamberInnerSystem1810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hGc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CG·CCC`: the faces of μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEFG52810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG52810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq6 hcq8 hcq9 hApos hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0654 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0655 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0566 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1008 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0657 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0658 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1009 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq6 hcq9 hcq0)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0573 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0661 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0576 A.natDegree B.natDegree C.natDegree G.natDegree h hcq2 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1010 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq9 hcq0)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq2 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0580 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0664 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0583 A.natDegree B.natDegree C.natDegree G.natDegree h hcq2 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0665 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hApos h hcq2 hcq1 hcq0)
  have hr0 : (muQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest7810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq2 hcq6; omega) (by clear * - hcq0 hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace7810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq6 hcq8 hcq9 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ 5 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + 3 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * E.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 4 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0666 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0667 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0566 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1011 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0668 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0669 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq9 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1012 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq6 hcq9 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + F.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree ∧ E.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0671 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0672 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0573 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1013 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0673 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0674 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq9 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1014 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq6 hcq9 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0676 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq2 hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0677 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0580 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1015 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0678 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0679 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq9 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1016 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq4 hcq2 hcq1 hcq6 hcq0)
  have hr1 : (piQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest1810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by clear * - hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq2 hcq6; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace1810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hdp1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticChamberInnerSystem5810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBDEFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0343 A.natDegree B.natDegree D.natDegree G.natDegree h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0807 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0682 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq8 hcq11 h hCn hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0683 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq11 h hCn hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0684 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq11 h hCn hcq5 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1017 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hcq11 h hcq5 hcq10 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0350 A.natDegree B.natDegree D.natDegree G.natDegree h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0812 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0687 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq8 hcq11 h hCn hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0688 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq11 h hCn hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0689 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq11 h hCn hcq5 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0690 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq8 hcq11 h hcq5 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0357 A.natDegree B.natDegree D.natDegree G.natDegree h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0818 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0190 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq8 hcq11 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0710 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 h hCn hcq5 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0193 A.natDegree B.natDegree C.natDegree G.natDegree hcq11 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0194 A.natDegree B.natDegree E.natDegree G.natDegree hcq8 hcq11 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0692 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq11 h hCn hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq11 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0693 A.natDegree B.natDegree E.natDegree G.natDegree hApos hcq8 hcq11 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0366 A.natDegree B.natDegree D.natDegree G.natDegree h hcq5 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0823 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq6 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0713 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0202 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq8 hcq11 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0715 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 h hCn hcq5 hcq10 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0205 A.natDegree B.natDegree C.natDegree G.natDegree hcq11 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0206 A.natDegree B.natDegree E.natDegree G.natDegree hcq8 hcq11 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0695 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq11 h hCn hcq5 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq11 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0716 A.natDegree B.natDegree F.natDegree G.natDegree hcq11 h hcq10 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0210 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq11 h hCn hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0377 A.natDegree B.natDegree D.natDegree G.natDegree h hcq5 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0827 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq6 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0717 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0213 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq6 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0696 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq11 hCn hcq5 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0216 A.natDegree B.natDegree C.natDegree hApos h hCn)
    · exact Or.inr (astra4u_Round4Package_nat_0217 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0697 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq11 hCn hcq5 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0219 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq11 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0387 A.natDegree B.natDegree D.natDegree G.natDegree h hcq11 hcq5 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz (by clear * - hcq5; omega) (by clear * - hcq0 hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq3 hcq5; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0832 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq8 hcq11 h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1018 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hcq11 h hcq1 hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0833 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq11 hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0834 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq11 hcq1 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0835 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq11 hcq10 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1019 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hcq11 h hcq3 hcq5 hcq7 hcq10 hcq0)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0837 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq6 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1020 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 h hcq1 hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0838 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq8 h hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0839 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq1 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0840 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq11 hcq10 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1021 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq6 hcq1 hcq5 hcq0)
  have hz1delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0729 A.natDegree B.natDegree F.natDegree G.natDegree hcq1 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0731 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0842 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos hcq6 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0732 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0733 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1022 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq3 hcq5 hcq0)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz (by clear * - hcq5; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq10; omega) (by clear * - hcq5; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq3 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hdp0 hdp1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face3_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticChamberInnerSystem1810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hGc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CG·CCC`: the faces of μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberCDEFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq5 hcq8 hcq10 hzero; omega)
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1023 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1024 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1025 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq8 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1026 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1027 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1028 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq11 hcq0)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1029 A.natDegree C.natDegree D.natDegree G.natDegree h hcq2 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1030 A.natDegree C.natDegree D.natDegree G.natDegree h hcq2 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1031 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq8 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1032 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1033 A.natDegree C.natDegree D.natDegree G.natDegree h hcq2 hcq11)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1034 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq11 hcq0)
  have hr0 : (muQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest7810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq11; omega) (by clear * - hcq0 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace7810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq5 hcq8 hcq10 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1035 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1036 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1037 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq8 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1038 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1039 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1040 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq8 hcq11 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ E.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1041 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1042 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1043 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq8 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1044 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1045 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1046 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq11 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree ∧ D.natDegree + E.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1048 A.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1049 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1050 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1051 A.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1052 A.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq11 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1053 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq6 hcq2 hcq1 hcq0)
  have hr1 : (piQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest1810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq2 hcq11; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq2 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace1810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticChamberInnerSystem5810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `DD·DF·DG·FF·FG·GG`: the faces of μ, ξ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberCDEFG44810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG44810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0845 A.natDegree C.natDegree D.natDegree G.natDegree hcq1 hAD h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1054 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0847 A.natDegree D.natDegree F.natDegree h hAD hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq1 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1055 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAD hcq0 hcq6 hcq10)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0851 A.natDegree C.natDegree D.natDegree G.natDegree hcq1 hAD h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1056 A.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0853 A.natDegree D.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0854 A.natDegree D.natDegree G.natDegree hApos h hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0855 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0 hcq6)
  have hr0 : (muQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest8810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz (by clear * - hAD hcq1 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq1 hcq10; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega))
  have hct0 := muQuarticChamberFace8810_coeff_top hAne hDne hFne (B := B) (C := C) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face8_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticChamberInner8810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0856 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0857 A.natDegree D.natDegree F.natDegree hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1057 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0858 A.natDegree D.natDegree F.natDegree h hAD hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0859 A.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1058 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAD hcq0 hcq6 hcq10)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0861 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0862 A.natDegree D.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1059 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0863 A.natDegree D.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0864 A.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1060 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq0 hcq6 hcq10)
  have hr1 : (xiQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest3810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz (by clear * - hAD hcq0 hcq1 hcq6 hcq10; omega) (by clear * - hAD hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq10; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hct1 := xiQuarticChamberFace3810_coeff_top hAne hDne hFne (B := B) (C := C) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hdp1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face3_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact quarticChamberInnerSystem7810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hFc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0335 A.natDegree B.natDegree D.natDegree G.natDegree h hcq17 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0407 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq20 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq20)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1061 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB h hcq0 hcq20 hcq5 hcq17 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0337 A.natDegree B.natDegree D.natDegree G.natDegree h hcq17 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0409 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq20 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq20)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0883 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAB h hcq0 hcq20 hcq17 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0339 A.natDegree B.natDegree D.natDegree G.natDegree h hcq17 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0410 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq20 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq20)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq20)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq20)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0340 A.natDegree B.natDegree D.natDegree G.natDegree h hcq17 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0411 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq20 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq20)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq20)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0146 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0341 A.natDegree B.natDegree D.natDegree G.natDegree h hcq17 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0412 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq20 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq17)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq20)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq17)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq17)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq20)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq17)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq17)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq17; omega) (by clear * - hcq4; omega) (by clear * - hcq5; omega) (by clear * - hcq8; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq5 hcq7 hcq17; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0236 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq20 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1062 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB h hcq0 hcq20 hcq5 hcq17 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0238 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq20 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0868 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAB hcq0 hcq20 hcq5 hcq17)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0240 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq20 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq17)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0155 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0244 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq5 hcq17)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq20; omega) (by clear * - hcq17; omega) (by clear * - hcq4; omega) (by clear * - hcq0 hcq5 hcq17; omega) (by clear * - hcq0 hcq11; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hcq5 hApos hcq17; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq17; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face3_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticChamberInnerSystem0810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc

end QuarticChamberKills4810

end Max11DegreeRoutes
/-! # Multi-carrier chamber kills, `(8,10)` scale zero

44 chambers whose certificate needs several faces: each face's top
coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`
bridge, and the isobaric identity then contradicts a product of
non-zero leading coefficients.  Untracked working note.
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

section QuarticChamberKills4810

/-! ## Multi-carrier chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·CF·BBB·BBC·BCC·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDEFG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG29810 A B C D E F G)
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0916 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0416 A.natDegree B.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0418 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0249 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1063 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq1 h hcq0 hcq6 hcq9 hcq14)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0918 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0423 A.natDegree B.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0425 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0255 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1064 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq1 h hcq0 hcq6 hcq9 hcq14)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0920 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0430 A.natDegree B.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0432 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0261 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0435 A.natDegree B.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0263 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0264 A.natDegree B.natDegree F.natDegree hcq1 h hcq14)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0437 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq0 hcq14)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0921 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0439 A.natDegree B.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0268 A.natDegree B.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0441 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0270 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0444 A.natDegree B.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0272 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0273 A.natDegree B.natDegree F.natDegree hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0274 A.natDegree B.natDegree F.natDegree hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0275 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0276 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq14)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0922 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq6 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0446 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq11 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0279 A.natDegree B.natDegree D.natDegree F.natDegree hApos hcq7 hcq1 h)
    · exact Or.inr (astra4u_Round4Package_nat_0280 A.natDegree B.natDegree F.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0447 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq11 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0282 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq7 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0449 A.natDegree B.natDegree E.natDegree F.natDegree h hcq11 hcq1 hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0284 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq9 hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0285 A.natDegree B.natDegree F.natDegree h hcq1 hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0287 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0288 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq9 hcq14)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq9; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq1 hcq7 hcq11; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0923 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0290 A.natDegree B.natDegree C.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0871 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0292 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0293 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0294 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1065 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq1 h hcq0 hcq6 hcq9 hcq14)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0925 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0297 A.natDegree B.natDegree C.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0873 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0299 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0300 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0301 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0874 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq0 hcq9 hcq14)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0926 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0304 A.natDegree B.natDegree C.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0875 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0306 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0307 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0308 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0309 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0310 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0311 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq9 hcq14)
  have hr1 : (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq11 hcq14; omega) (by clear * - hcq9; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq11; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega))
  have hct1 := muQuarticChamberFace9810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0927 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0313 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0876 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0315 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0316 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0317 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1066 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq1 h hcq0 hcq6 hcq9 hcq14)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0929 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0320 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0878 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0322 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0323 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0324 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0879 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 hcq1 h hcq0 hcq9 hcq14)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0930 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0327 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0880 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0329 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0330 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq9 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0331 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0332 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0333 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq14)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0881 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq11 hcq1 hcq0 hcq9 hcq14)
  have hr2 : (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest2000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by clear * - hcq9; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq1 hcq7 hcq11; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq11 hcq14; omega) (by clear * - hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq1 hcq6 hcq9; omega) (by clear * - hcq1 hcq11 hcq14; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq1 hcq7 hcq9 hcq11; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos hcq11; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega))
  have hct2 := piQuarticChamberFace2000810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face2000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact quarticNoTargetInner_ABCF_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff hin0 hin1 hin2 hAc hBc hCc hFc

end QuarticChamberKills4810

end Max11DegreeRoutes
