import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart00Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests4Scratch
import Grok810ScaleZeroQuarticChamberInnerScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch

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
/-- Chamber `BEFG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBEFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0806 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0807 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0808 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0172 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAC hcq4 hcq7 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0173 A.natDegree B.natDegree D.natDegree G.natDegree hcq7 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0809 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hAD h hCn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0175 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq7 h hCn hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0810 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq7 h hcq6 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0811 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0812 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0813 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0181 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAC hcq4 hcq7 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0814 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0815 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 hAD h hCn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0816 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq7 h hCn hcq6 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0185 A.natDegree B.natDegree E.natDegree G.natDegree hcq4 hcq7 h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0817 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0818 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0819 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0190 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq4 hcq7 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0820 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0821 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hAD hCn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0193 A.natDegree B.natDegree C.natDegree G.natDegree hcq7 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0194 A.natDegree B.natDegree E.natDegree G.natDegree hcq4 hcq7 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0822 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hAD hCn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq7 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0693 A.natDegree B.natDegree E.natDegree G.natDegree hApos hcq4 hcq7 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0198 A.natDegree B.natDegree D.natDegree G.natDegree hcq7 h hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0823 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq2 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0200 A.natDegree B.natDegree D.natDegree G.natDegree h hcq7 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0713 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0202 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq4 hcq7 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0824 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hDn hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0825 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hAD hCn hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0205 A.natDegree B.natDegree C.natDegree G.natDegree hcq7 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0206 A.natDegree B.natDegree E.natDegree G.natDegree hcq4 hcq7 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0826 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hAD hCn hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq7 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0716 A.natDegree B.natDegree F.natDegree G.natDegree hcq7 h hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0210 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq7 h hCn hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0211 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0827 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq2 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0717 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0213 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq2 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0828 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hDn hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0829 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hCn hDn hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0216 A.natDegree B.natDegree C.natDegree hApos h hCn)
    · exact Or.inr (astra4u_Round4Package_nat_0217 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq2 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0830 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hCn hDn hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0219 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq7 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0831 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hDn hcq6 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hDz hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hDn hdp0; omega)
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
  have hz1l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0832 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq7 h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0833 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq7 hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0834 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq7 hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0835 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq7 hcq6 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0836 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq7 h hcq3 hcq6 hcq0)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0837 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq2 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0838 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0839 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0840 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq7 hcq6 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0841 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq2 hcq1 hcq0)
  have hz1delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0729 A.natDegree B.natDegree F.natDegree G.natDegree hcq1 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0842 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos hcq2 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0732 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0733 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0843 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq2 hcq0)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hDz (by clear * - hcq6; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hDn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hDn hdp0 hdp1; omega)
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
/-- Chamber `CDFG` / `DD·DF·DG·FF·FG·GG`: the faces of μ, ξ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberCDFG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0845 A.natDegree C.natDegree D.natDegree G.natDegree hcq1 hAD h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0847 A.natDegree D.natDegree F.natDegree h hAD hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq1 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0849 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAD hcq0 hcq6)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0851 A.natDegree C.natDegree D.natDegree G.natDegree hcq1 hAD h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0853 A.natDegree D.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0854 A.natDegree D.natDegree G.natDegree hApos h hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0855 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0 hcq6)
  have hr0 : (muQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest8810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz hEz (by clear * - hAD hcq1 hcq6; omega) (by clear * - hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega))
  have hct0 := muQuarticChamberFace8810_coeff_top hAne hDne hFne (B := B) (C := C) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0856 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0857 A.natDegree D.natDegree F.natDegree hAD h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0858 A.natDegree D.natDegree F.natDegree h hAD hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0859 A.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0860 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hAD hcq0 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0861 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0862 A.natDegree D.natDegree F.natDegree hApos h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0863 A.natDegree D.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0864 A.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0865 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos hcq1 h hcq0 hcq6)
  have hr1 : (xiQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest3810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz hEz (by clear * - hAD hcq0 hcq1 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hct1 := xiQuarticChamberFace3810_coeff_top hAne hDne hFne (B := B) (C := C) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdp0 hdp1; omega)
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
/-- Chamber `BCDEF` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDEF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0081 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq11 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0407 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0866 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hAB h hcq0 hcq14 hcq4 hcq11)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0086 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq11 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0409 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0235 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hAB h hcq0 hcq14 hcq11)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0091 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq11 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0410 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq14)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0096 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq11 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0411 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0146 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0101 A.natDegree B.natDegree D.natDegree G.natDegree h hAB hcq11 hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0412 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq11)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by clear * - hcq11; omega) (by clear * - hcq4; omega) (by clear * - hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq4 hcq5 hcq11; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0236 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq14 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0867 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hAB h hcq0 hcq14 hcq4 hcq11)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0238 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq14 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0868 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAB hcq0 hcq14 hcq4 hcq11)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0240 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq14 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0155 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0244 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq4 hcq11)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq4 hcq11; omega) (by clear * - hcq0 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hApos hcq11; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1; omega)
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
/-- Chamber `BCDEF` / `BF·CF·BBB·BBC·BCC·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDEF5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF5810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0245 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAG h hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0416 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0418 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0249 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0869 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hcq7 hcq10)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0251 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAG h hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0423 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0425 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0255 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0870 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hcq7 hcq10)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0257 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0430 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0432 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0261 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0435 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0263 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0264 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0437 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hcq10)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0266 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0439 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0268 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0441 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0270 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0444 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0272 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0273 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0274 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0275 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0276 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0277 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq7 hcq10 hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0446 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq8 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0279 A.natDegree B.natDegree D.natDegree F.natDegree hApos hcq5 hcq1 h)
    · exact Or.inr (astra4u_Round4Package_nat_0280 A.natDegree B.natDegree F.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0447 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq8 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0282 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq5 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0449 A.natDegree B.natDegree E.natDegree F.natDegree h hcq8 hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0284 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq7 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0285 A.natDegree B.natDegree F.natDegree h hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0287 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0288 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq7 hcq10)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by clear * - hcq7; omega) (by clear * - hcq1 hcq5 hcq8; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0289 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0290 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0871 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0292 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0293 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0294 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0872 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hcq7 hcq10)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0296 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0297 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0873 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0299 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0300 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0301 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0874 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hcq7 hcq10)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0303 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0304 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0875 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0306 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0307 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0308 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0309 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0310 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0311 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq7 hcq10)
  have hr1 : (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq0 hcq8 hcq10; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hct1 := muQuarticChamberFace9810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1; omega)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0312 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0313 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0876 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0315 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0316 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0317 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0877 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hcq7 hcq10)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0319 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0320 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0878 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0322 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0323 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0324 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0879 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq1 h hcq0 hcq7 hcq10)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0326 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq10 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0327 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0880 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0329 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0330 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq7 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0331 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0332 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0333 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0881 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq1 hcq0 hcq7 hcq10)
  have hr2 : (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest2000810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hGz (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq1 hcq5 hcq8; omega) (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq8 hcq10; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq1 hcq8 hcq10; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq1 hcq5 hcq7 hcq8; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hct2 := piQuarticChamberFace2000810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hGn hdp0 hdp1 hdp2; omega)
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
/-- Chamber `BCDEG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDEG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0335 A.natDegree B.natDegree D.natDegree G.natDegree h hcq11 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0116 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq14 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0882 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAB h hcq0 hcq14 hcq11 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0337 A.natDegree B.natDegree D.natDegree G.natDegree h hcq11 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0119 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq14 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0883 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAB h hcq0 hcq14 hcq11 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0339 A.natDegree B.natDegree D.natDegree G.natDegree h hcq11 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0122 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq14 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq14)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0340 A.natDegree B.natDegree D.natDegree G.natDegree h hcq11 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0126 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq14 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0341 A.natDegree B.natDegree D.natDegree G.natDegree h hcq11 hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0129 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq14 hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq14)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq11)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq11)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by clear * - hcq11; omega) (by clear * - hcq3; omega) (by clear * - hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta (Or.inr (by clear * - hcq5 hApos; omega)) hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0236 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq14 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0884 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAB h hcq0 hcq14 hcq11 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0238 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq14 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0239 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hAB hcq0 hcq14 hcq11)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0240 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq14 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0115 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq11)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq11; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega)
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
/-- Chamber `BCDEG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDEG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
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
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0343 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0681 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq7 h hcq4 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0345 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq4 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0478 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0347 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0348 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq7 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0885 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 hcq7 h hcq4 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0350 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0686 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq7 h hcq4 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0352 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq4 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0482 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0354 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0355 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq7 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0886 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 hcq7 h hcq4 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0357 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0187 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq7 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0359 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq4 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0489 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0361 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0362 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq7 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0194 A.natDegree B.natDegree E.natDegree G.natDegree hcq6 hcq7 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0364 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq7 h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq7 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0493 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 hcq6 hcq7 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0366 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0199 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq7 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0368 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq4 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0495 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0370 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0371 A.natDegree B.natDegree C.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0206 A.natDegree B.natDegree E.natDegree G.natDegree hcq6 hcq7 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0373 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq7 h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq7 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0374 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq4 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0375 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq7 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0376 A.natDegree B.natDegree C.natDegree hApos h hcq1)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0377 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0500 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq6 hcq7 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0379 A.natDegree B.natDegree F.natDegree G.natDegree h hcq7 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0501 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq1 hcq5 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0381 A.natDegree B.natDegree C.natDegree D.natDegree h hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0382 A.natDegree B.natDegree C.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0217 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq5 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0384 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq7 hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0385 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hcq4 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0386 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq7 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0387 A.natDegree B.natDegree D.natDegree G.natDegree h hcq7 hcq4 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by clear * - hcq4; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq1; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0507 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq6 hcq7 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0508 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq6 hcq7 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0887 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 hcq7 h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0509 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq6 hcq7 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0510 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq6 hcq7 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0888 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 hcq7 h hcq3 hcq4 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0512 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 h hcq5 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0513 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0889 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq1 hcq6 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0514 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0515 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq6 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0890 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 hcq7 h hcq5 hcq4 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0400 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0401 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0402 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0518 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 hcq5 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0405 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0891 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq1 hcq3 hcq4 hcq0)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by clear * - hcq4; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq4; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq0 hcq3 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega)
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
/-- Chamber `BCDEG` / `CG·CCC`: the faces of μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDEG28810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG28810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq4 hcq6 hcq7 hApos hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0892 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0893 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0894 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0895 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq2 hcq6 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0568 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0896 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0897 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq2 hcq6 hcq7 hcq0)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0898 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq1 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0575 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0576 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0899 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq2 hcq6 hcq7 hcq0)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0900 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq1 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0582 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0583 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0901 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hApos h hcq1 hcq2 hcq7 hcq0)
  have hr0 : (muQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest7810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq0 hcq5; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hct0 := muQuarticChamberFace7810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega)
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
    exact hnc (by clear * - hFn hcq0 hcq1 hcq4 hcq6 hcq7 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ 5 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ B.natDegree + 3 * C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * E.natDegree < 4 * C.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0902 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0903 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0904 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0905 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq2 hcq6 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0568 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0906 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0907 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq2 hcq6 hcq7 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * D.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0642 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0643 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0908 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0644 A.natDegree B.natDegree C.natDegree E.natDegree h hcq1 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0575 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0909 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0910 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq2 hcq6 hcq7 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ D.natDegree + E.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0647 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0648 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0911 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0649 A.natDegree B.natDegree C.natDegree E.natDegree h hcq1 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0582 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0912 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0913 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq5 hcq1 hcq2 hcq6 hcq7 hcq0)
  have hr1 : (piQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by clear * - hcq1; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq2 hcq5; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq0 hcq1 hcq2 hcq7; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq2 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace1810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega)
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
/-- Chamber `BCDFG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0335 A.natDegree B.natDegree D.natDegree G.natDegree h hcq13 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0137 A.natDegree B.natDegree E.natDegree F.natDegree hApos hAB hcq10 h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0914 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq0 hcq5 hcq13 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0337 A.natDegree B.natDegree D.natDegree G.natDegree h hcq13 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0140 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0338 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAB h hcq0 hcq13 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0339 A.natDegree B.natDegree D.natDegree G.natDegree h hcq13 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0142 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0340 A.natDegree B.natDegree D.natDegree G.natDegree h hcq13 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0144 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAB h hcq0 hcq5 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0146 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0341 A.natDegree B.natDegree D.natDegree G.natDegree h hcq13 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0147 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq5 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq13)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq13)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq13)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq13)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq13)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by clear * - hcq13; omega) (by clear * - hcq4; omega) (by clear * - hcq5; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq5 hcq7 hcq13; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0107 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq13 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0915 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hAB h hcq0 hcq5 hcq13 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0110 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq13 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0243 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hAB hcq0 hcq5 hcq13)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0113 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq13 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0155 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0244 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq5 hcq13)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq13; omega) (by clear * - hcq4; omega) (by clear * - hcq0 hcq5 hcq13; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hcq5 hApos hcq13; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega)
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
/-- Chamber `BCDFG` / `BF·CF·BBB·BBC·BCC·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG17810 A B C D E F G)
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
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0916 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0246 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0248 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0249 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0917 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8 hcq10)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0918 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0252 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0254 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0255 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0919 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8 hcq10)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0920 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0258 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0260 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0261 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0262 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 hAE h hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0263 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0264 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0265 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0921 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0267 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0268 A.natDegree B.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0269 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 h hcq0 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0270 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0271 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0272 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0273 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0274 A.natDegree B.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0275 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0276 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0922 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq6 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0278 A.natDegree B.natDegree E.natDegree F.natDegree h hEn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0279 A.natDegree B.natDegree D.natDegree F.natDegree hApos hcq7 hcq1 h)
    · exact Or.inr (astra4u_Round4Package_nat_0280 A.natDegree B.natDegree F.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0281 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq1 hcq0 hEn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0282 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq7 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0283 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq8 hEn hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0284 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq8 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0285 A.natDegree B.natDegree F.natDegree h hcq1 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0287 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
    · exact Or.inr (astra4u_Round4Package_nat_0288 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq8 hcq10)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0923 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0290 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0291 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0292 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0293 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0294 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0924 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8 hcq10)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0925 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0297 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0298 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0299 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0300 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0301 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0302 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0926 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0304 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0305 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0306 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0307 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0308 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0309 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0310 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0311 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq8 hcq10)
  have hr1 : (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega))
  have hct1 := muQuarticChamberFace9810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0927 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0313 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0314 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0315 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0316 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0317 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0928 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq8 hcq10)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0929 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0320 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0321 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0322 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0323 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0324 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0325 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0930 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq6 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0327 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0328 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq8 hEn hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0329 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0330 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0331 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0332 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0333 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0334 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq8 hcq10)
  have hr2 : (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest2000810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq10; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq1 hcq6 hcq8; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega))
  have hct2 := piQuarticChamberFace2000810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1 hdp2; omega)
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
/-- Chamber `BCDFG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDFG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG27810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0343 A.natDegree B.natDegree D.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0702 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq9 h hcq6 hEn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0346 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq9 h hcq6 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0347 A.natDegree B.natDegree C.natDegree D.natDegree hcq3 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0348 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0931 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq9 h hcq6 hcq8 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0350 A.natDegree B.natDegree D.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0705 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq9 h hcq6 hEn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0353 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq9 h hcq6 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0354 A.natDegree B.natDegree C.natDegree D.natDegree hcq3 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0355 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0356 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 h hcq6 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0357 A.natDegree B.natDegree D.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0708 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq9 h hcq6 hEn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0360 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq9 h hcq6 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0361 A.natDegree B.natDegree C.natDegree D.natDegree hcq3 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0362 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0363 A.natDegree B.natDegree E.natDegree G.natDegree hcq9 hAE h hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0364 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq9 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0365 A.natDegree B.natDegree C.natDegree G.natDegree hApos hcq3 hcq9 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0366 A.natDegree B.natDegree D.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0712 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq9 h hEn hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0713 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0369 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 hcq9 h hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0370 A.natDegree B.natDegree C.natDegree D.natDegree hcq3 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0371 A.natDegree B.natDegree C.natDegree hApos hcq3 h)
      · exact Or.inr (astra4u_Round4Package_nat_0372 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq9 h hcq6 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0373 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq3 hcq9 h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq9 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0716 A.natDegree B.natDegree F.natDegree G.natDegree hcq9 h hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0375 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 hcq9 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0376 A.natDegree B.natDegree C.natDegree hApos h hcq3)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0377 A.natDegree B.natDegree D.natDegree G.natDegree h hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0278 A.natDegree B.natDegree E.natDegree F.natDegree h hEn hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0717 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0380 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq3 hcq9 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0381 A.natDegree B.natDegree C.natDegree D.natDegree h hcq3 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0382 A.natDegree B.natDegree C.natDegree hApos h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0383 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq9 hcq6 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0384 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq3 hcq9 hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0386 A.natDegree B.natDegree C.natDegree G.natDegree h hcq3 hcq9 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0387 A.natDegree B.natDegree D.natDegree G.natDegree h hcq9 hcq6 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by clear * - hcq6; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq3; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0932 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 hcq9 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0933 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 hcq9 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0934 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq9 h hcq1 hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0935 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq9 hcq1 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0936 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq9 hcq8 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0937 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq9 h hcq6 hcq8 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0938 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0939 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0940 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0941 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0942 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq9 hcq8 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0943 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos hcq3 hcq9 h hcq1 hcq6 hcq8 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0944 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0945 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0946 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0947 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0948 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hApos h hcq3 hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0949 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq3 hcq1 hcq2 hcq6 hcq0)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by clear * - hcq6; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq3 hcq9; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq8; omega) (by clear * - hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdp0 hdp1; omega)
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
