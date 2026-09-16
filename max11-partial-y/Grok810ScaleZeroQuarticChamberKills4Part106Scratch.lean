import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart101Scratch
import Grok810ScaleZeroQuarticChamberDefs1Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests4Scratch
import Grok810ScaleZeroQuarticChamberInnerScratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberRestsScratch

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
/-- Chamber `BC` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBC1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBC1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFz, hGz, hcq0, hcq1, hcq2⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0000 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0001 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0008 A.natDegree B.natDegree C.natDegree hAB h hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0009 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0010 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0017 A.natDegree B.natDegree C.natDegree hAB h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0018 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0019 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0030 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0031 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0039 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0044 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0045 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BC l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hEz hFz hGz hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0060 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0064 A.natDegree B.natDegree C.natDegree hAB h hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0067 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0071 A.natDegree B.natDegree C.natDegree h hAB hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0074 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos h hcq0 hDn hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0076 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0080 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BC l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hEz hFz hGz (by clear * - hAB hcq0; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hGn hdp0 hdp1; omega)
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
/-- Chamber `BCD` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCD1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCD1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0081 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq4 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0001 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0085 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0086 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq4 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0010 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0090 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0091 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq4 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0019 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0096 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq4 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0031 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0101 A.natDegree B.natDegree D.natDegree G.natDegree h hAB hcq4 hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0045 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq4)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hFz hGz (by clear * - hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta (Or.inr (by clear * - hcq3 hApos; omega)) hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hApos hAB hAC hAD hAE hAF hAG hEn hFn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0107 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0109 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0110 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0112 A.natDegree B.natDegree C.natDegree D.natDegree h hAB hcq0 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0113 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0115 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq4)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hFz hGz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hApos hAB hAC hAD hAE hAF hAG hEn hFn hGn hdp0 hdp1; omega)
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
/-- Chamber `BCE` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCE1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCE1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0000 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0116 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0118 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq5)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0009 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0119 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0121 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq5)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0018 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0122 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq5)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0030 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0126 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0039 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0044 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0129 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq5 hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz hGz hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hApos hAB hAC hAD hAE hAF hAG hDn hFn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq5 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0133 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq5)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq5 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0135 A.natDegree B.natDegree C.natDegree E.natDegree h hAB hcq0 hcq5)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0136 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq5 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0076 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0080 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz hGz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hApos hAB hAC hAD hAE hAF hAG hDn hFn hGn hdp0 hdp1; omega)
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
/-- Chamber `BCF` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0000 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0137 A.natDegree B.natDegree E.natDegree F.natDegree hApos hAB hcq5 h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0139 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0009 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0140 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0017 A.natDegree B.natDegree C.natDegree hAB h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0018 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0142 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0030 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0144 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0039 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0146 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0044 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0147 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq4 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hEz hGz (by clear * - hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0060 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0151 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0067 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0153 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0074 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos h hcq0 hDn hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0076 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0155 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0156 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hEz hGz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hGn hdp0 hdp1; omega)
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
/-- Chamber `BCG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0157 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0001 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0158 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0159 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0010 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0160 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0161 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0019 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0162 A.natDegree B.natDegree D.natDegree G.natDegree hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0031 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0039 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0163 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0045 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hEz hFz (by clear * - hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0060 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0165 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0067 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0071 A.natDegree B.natDegree C.natDegree h hAB hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0074 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos h hcq0 hDn hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0076 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0080 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hEz hFz (by clear * - hAB hcq0; omega) (by clear * - hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hApos hAB hAC hAD hAE hAF hAG hDn hEn hFn hdp0 hdp1; omega)
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
/-- Chamber `BEG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBEG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0168 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0169 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq3 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0170 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0171 A.natDegree B.natDegree F.natDegree G.natDegree hcq3 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0172 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAC hcq2 hcq3 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0173 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0174 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 hAD h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0175 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq3 h hCn hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0176 A.natDegree B.natDegree E.natDegree G.natDegree hcq2 hcq3 h hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0177 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0178 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq3 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0179 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0180 A.natDegree B.natDegree F.natDegree G.natDegree hcq3 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0181 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAC hcq2 hcq3 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0182 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0183 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 hAD h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0184 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq3 h hCn hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0185 A.natDegree B.natDegree E.natDegree G.natDegree hcq2 hcq3 h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0186 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0187 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq3 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0188 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0189 A.natDegree B.natDegree F.natDegree G.natDegree hcq3 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0190 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hcq3 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0191 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0192 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 h hAD hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0193 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0194 A.natDegree B.natDegree E.natDegree G.natDegree hcq2 hcq3 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0195 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 h hAD hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq3 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0197 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq1 hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0198 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 h hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0199 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq3 h hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0200 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0201 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq3 h hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0202 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hcq3 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0203 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 h hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0204 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 h hAD hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0205 A.natDegree B.natDegree C.natDegree G.natDegree hcq3 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0206 A.natDegree B.natDegree E.natDegree G.natDegree hcq2 hcq3 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0207 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 h hAD hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq3 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0209 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq3 h hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0210 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq3 h hCn hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0211 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0212 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq1 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0213 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq1 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0214 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hcq3 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0215 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hCn hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0216 A.natDegree B.natDegree C.natDegree hApos h hCn)
    · exact Or.inr (astra4u_Round4Package_nat_0217 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0218 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hCn hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0219 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq3 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hDz hFz hz0l hz0beta hz0delta hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hDn hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0220 A.natDegree B.natDegree E.natDegree G.natDegree hcq2 hcq3 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0223 A.natDegree B.natDegree E.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0225 A.natDegree B.natDegree E.natDegree G.natDegree h hcq2 hcq3 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0226 A.natDegree B.natDegree E.natDegree G.natDegree hcq2 hcq3 h hcq0)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0227 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0230 A.natDegree B.natDegree E.natDegree hcq2 h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0232 A.natDegree B.natDegree E.natDegree G.natDegree h hcq2 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0233 A.natDegree B.natDegree E.natDegree h)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hDz hFz hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hDn hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hDn hFn hdp0 hdp1; omega)
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
/-- Chamber `BCDE` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDE1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0081 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq6 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0116 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0234 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hAB h hcq0 hcq9 hcq6)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0086 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq6 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0119 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0235 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hAB h hcq0 hcq9 hcq6)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0091 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq6 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0122 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq9)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0096 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq6 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0126 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0101 A.natDegree B.natDegree D.natDegree G.natDegree h hAB hcq6 hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0129 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq9 hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq6)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz hGz (by clear * - hcq6; omega) (by clear * - hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta (Or.inr (by clear * - hcq3 hApos; omega)) hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0236 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0237 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hAB h hcq0 hcq9 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0238 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0239 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hAB hcq0 hcq9 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0240 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq0 hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0115 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq6)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz hGz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hApos hAB hAC hAD hAE hAF hAG hFn hGn hdp0 hdp1; omega)
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
/-- Chamber `BCDF` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0081 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq8 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0137 A.natDegree B.natDegree E.natDegree F.natDegree hApos hAB hcq7 h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0241 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAB h hcq0 hcq4 hcq8)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0086 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq8 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0140 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0090 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0091 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq8 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0142 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0096 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hcq8 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0144 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAB h hcq0 hcq4 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0146 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0101 A.natDegree B.natDegree D.natDegree G.natDegree h hAB hcq8 hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0147 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq4 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq8)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hGz (by clear * - hcq8; omega) (by clear * - hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq4 hcq5 hcq8; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0107 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0242 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAB h hcq0 hcq4 hcq8)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0110 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0243 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hAB hcq0 hcq4 hcq8)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0113 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0155 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0244 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq4 hcq8)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hGz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq4 hcq8; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hcq8 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0 hdp1; omega)
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
/-- Chamber `BCDF` / `BF·CF·BBB·BBC·BCC·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDF5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF5810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0245 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAG h hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0246 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0248 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0249 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0250 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0251 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 hAG h hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0252 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0254 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0255 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0256 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0257 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0258 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0260 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0261 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0262 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 hAE h hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0263 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0264 A.natDegree B.natDegree F.natDegree hcq1 h hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0265 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0266 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0267 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0268 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0269 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 h hcq0 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0270 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0271 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0272 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0273 A.natDegree B.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0274 A.natDegree B.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0275 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0276 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0277 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq7 hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0278 A.natDegree B.natDegree E.natDegree F.natDegree h hEn hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0279 A.natDegree B.natDegree D.natDegree F.natDegree hApos hcq5 hcq1 h)
    · exact Or.inr (astra4u_Round4Package_nat_0280 A.natDegree B.natDegree F.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0281 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq1 hcq0 hEn hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0282 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq5 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0283 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq6 hEn hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0284 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq6 hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0285 A.natDegree B.natDegree F.natDegree h hcq1 hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0287 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0288 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hcq6 hcq7)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hGz (by clear * - hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0289 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0290 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0291 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0292 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0293 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0294 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0295 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0296 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0297 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0298 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0299 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0300 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0301 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0302 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0303 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0304 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0305 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0306 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0307 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0308 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0309 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0310 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0311 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq6 hcq7)
  have hr1 : (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hGz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hct1 := muQuarticChamberFace9810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0 hdp1; omega)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0312 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0313 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0314 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0315 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0316 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0317 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0318 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0319 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0320 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0321 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hAE h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0322 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0323 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0324 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0325 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0326 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0327 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0328 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq6 hEn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0329 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0330 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hcq6 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0331 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0332 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0333 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0334 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq0 hcq6 hcq7)
  have hr2 : (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest2000810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz hGz (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq7; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hct2 := piQuarticChamberFace2000810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hGn hdp0 hdp1 hdp2; omega)
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
/-- Chamber `BCDG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0335 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0001 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0084 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0336 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAB h hcq0 hcq8 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0337 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0010 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0089 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0338 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAB h hcq0 hcq8 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0339 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0019 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hAF hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0094 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0095 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0340 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0031 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0099 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0100 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0341 A.natDegree B.natDegree D.natDegree G.natDegree h hcq8 hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0045 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hEn hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0104 A.natDegree B.natDegree C.natDegree D.natDegree h hcq0 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0105 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0106 A.natDegree B.natDegree D.natDegree h hAB hcq8)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hFz (by clear * - hcq8; omega) (by clear * - hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta (Or.inr (by clear * - hcq5 hApos; omega)) hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0107 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0108 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0342 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAB h hcq0 hcq8 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0110 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0111 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0112 A.natDegree B.natDegree C.natDegree D.natDegree h hAB hcq0 hcq8)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0113 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq8 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0114 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0115 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hcq8)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hFz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq8; omega) (by clear * - hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdp1; omega)
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
/-- Chamber `BCDG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCDG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0343 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0344 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hAF hcq3 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0345 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0346 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq4 h hcq3 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0347 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0348 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0349 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hcq3 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0350 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0351 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hAF hcq3 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0352 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0353 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq4 h hcq3 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0354 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0355 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0356 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hcq3 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0357 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0358 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hAF hcq3 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0359 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0360 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq4 h hcq3 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0361 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0362 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0363 A.natDegree B.natDegree E.natDegree G.natDegree hcq4 hAE h hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0364 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq4 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0365 A.natDegree B.natDegree C.natDegree G.natDegree hApos hcq1 hcq4 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0366 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0367 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq3 hEn hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0368 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0369 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq4 h hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0370 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0371 A.natDegree B.natDegree C.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0372 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq4 h hcq3 hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0373 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0374 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq4 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0375 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0376 A.natDegree B.natDegree C.natDegree hApos h hcq1)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0377 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0378 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq3 hEn hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0379 A.natDegree B.natDegree F.natDegree G.natDegree h hcq4 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0380 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq4 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0381 A.natDegree B.natDegree C.natDegree D.natDegree h hcq1 hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0382 A.natDegree B.natDegree C.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0383 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq4 hcq3 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0384 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq4 hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0385 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq4 hcq3 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0386 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0387 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq3 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hFz (by clear * - hcq3; omega) (by clear * - hcq1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq1; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0388 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0389 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0390 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0392 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0393 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hcq3 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0394 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0395 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0396 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0398 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0399 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hApos hcq1 hcq4 h hcq3 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0400 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0401 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0402 A.natDegree B.natDegree C.natDegree D.natDegree hcq1 h hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0405 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0406 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq1 hcq3)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hFz (by clear * - hcq3; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq3; omega) (by clear * - hcq1 hcq3; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdp0 hdp1; omega)
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
/-- Chamber `BCEF` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0000 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0407 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq9 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0408 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAB h hcq0 hcq9 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0009 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAG h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0409 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq9 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0121 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq9)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0018 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0410 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq9 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq9)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0030 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0411 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq9 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0039 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0146 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0044 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0412 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq9 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hGz (by clear * - hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0058 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0413 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAB h hcq0 hcq9 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0065 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0414 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq9 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0072 A.natDegree B.natDegree C.natDegree G.natDegree hApos hAB h hcq0 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0136 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0076 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0155 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0156 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq4)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hGz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq4 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0 hdp1; omega)
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
/-- Chamber `BCEF` / `BF·CF·BBB·BBC·BCC·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEF5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEF5810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0415 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 hAG h hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0416 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0417 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 hAD h hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0418 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0419 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 hAD h hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0420 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0249 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0421 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq0 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0422 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 hAG h hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0423 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0424 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 h hAD hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0425 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0426 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0427 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0255 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0428 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq0 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0429 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hDn hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0430 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0431 A.natDegree B.natDegree D.natDegree F.natDegree hcq1 h hAD hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0432 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0433 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0434 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0261 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0435 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0436 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0264 A.natDegree B.natDegree F.natDegree hcq1 h hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0437 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq0 hcq7)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0438 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hDn hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0439 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0440 A.natDegree B.natDegree D.natDegree F.natDegree h hcq1 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0268 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0441 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0442 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0443 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0270 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0444 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0445 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0273 A.natDegree B.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0274 A.natDegree B.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0275 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0276 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0044 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hGn)
    · exact Or.inr (astra4u_Round4Package_nat_0446 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq5 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0280 A.natDegree B.natDegree F.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0447 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq5 hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0448 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hDn hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0449 A.natDegree B.natDegree E.natDegree F.natDegree h hcq5 hcq1 hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0450 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0 hDn hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0285 A.natDegree B.natDegree F.natDegree h hcq1 hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0287 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hGz hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0451 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq0 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0290 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0452 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 hAD h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0292 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0453 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0294 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0454 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq0 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0455 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hcq0 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0297 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0456 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0299 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0457 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0301 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0458 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq0 hcq7)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0459 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hcq0 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0304 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0460 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0306 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0461 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0308 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0309 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0310 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0462 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
  have hr1 : (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest9810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hGz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq0 hcq1 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace9810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0 hdp1; omega)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0463 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq0 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0313 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0464 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 hAD h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0315 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0465 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 hAD h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0317 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0466 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq0 hcq7)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0467 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hcq0 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0320 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0468 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0322 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0469 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0324 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0470 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq5 hcq1 h hcq0 hcq7)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0471 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hcq0 hcq7 hGn)
      · exact Or.inr (astra4u_Round4Package_nat_0327 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0472 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 hcq1 h hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0329 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0473 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hAD hcq0 hDn hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0331 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0332 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0333 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0474 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq5 hcq1 hcq0 hcq7)
  have hr2 : (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest2000810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz hGz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq1 hcq5 hcq7; omega) (by clear * - hcq0 hcq1 hcq5; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct2 := piQuarticChamberFace2000810_coeff_top hAne hBne hCne hFne (D := D) (E := E) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hGn hdp0 hdp1 hdp2; omega)
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
/-- Chamber `BCEG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0157 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0116 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0003 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0117 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0475 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAB h hcq0 hcq9 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0159 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0119 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0012 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0120 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0476 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAB h hcq0 hcq9 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0161 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0122 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0021 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0123 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0124 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0125 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq9)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0162 A.natDegree B.natDegree D.natDegree G.natDegree hAB h hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0126 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0033 A.natDegree B.natDegree F.natDegree hApos hAB h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0127 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0128 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_0039 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0040 A.natDegree B.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_0041 A.natDegree B.natDegree F.natDegree hApos h hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0042 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0043 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0163 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0129 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq9 hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0047 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0130 A.natDegree B.natDegree C.natDegree E.natDegree h hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0131 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hcq9)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0055 A.natDegree B.natDegree F.natDegree hApos h hFn)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz (by clear * - hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0059 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0477 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAB h hcq0 hcq9 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0066 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0135 A.natDegree B.natDegree C.natDegree E.natDegree h hAB hcq0 hcq9)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0073 A.natDegree B.natDegree C.natDegree F.natDegree hApos hAB h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0136 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAB h hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0075 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0076 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0077 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0078 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0079 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0080 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hr1 : (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest3810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq5; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega)
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
/-- Chamber `BCEG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0168 A.natDegree B.natDegree D.natDegree G.natDegree hcq4 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0169 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq4 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0170 A.natDegree B.natDegree D.natDegree G.natDegree hcq4 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0171 A.natDegree B.natDegree F.natDegree G.natDegree hcq4 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0478 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq3 h)
      · exact Or.inr (astra4u_Round4Package_nat_0173 A.natDegree B.natDegree D.natDegree G.natDegree hcq4 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0479 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0348 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0480 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq3 hcq4 h hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0177 A.natDegree B.natDegree D.natDegree G.natDegree hcq4 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0178 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq4 h hAF hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0179 A.natDegree B.natDegree D.natDegree G.natDegree hcq4 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0481 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hcq4 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0482 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq3 h)
      · exact Or.inr (astra4u_Round4Package_nat_0483 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0484 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 hAD h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0355 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0485 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq3 hcq4 h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0486 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0187 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq4 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0487 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0488 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hcq4 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0489 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq3 h)
      · exact Or.inr (astra4u_Round4Package_nat_0490 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0491 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0362 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0194 A.natDegree B.natDegree E.natDegree G.natDegree hcq3 hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0492 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hAD hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq4 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0493 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 hcq3 hcq4 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0198 A.natDegree B.natDegree D.natDegree G.natDegree hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0199 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq4 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0200 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0494 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hcq4 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0495 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0496 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0497 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0371 A.natDegree B.natDegree C.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0206 A.natDegree B.natDegree E.natDegree G.natDegree hcq3 hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0498 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq3 hcq4 h hDn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0499 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hcq4 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0375 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 hcq4 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0376 A.natDegree B.natDegree C.natDegree hApos h hcq1)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0211 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0500 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq4 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0379 A.natDegree B.natDegree F.natDegree G.natDegree h hcq4 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0501 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq1 hcq2 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0502 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq4 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0503 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq4 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0382 A.natDegree B.natDegree C.natDegree hApos h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_0217 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq2 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0504 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq4 hDn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0505 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq4 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0386 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0506 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hcq4 hDn hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz (by clear * - hcq1; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq1; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0507 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq3 hcq4 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0508 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq3 hcq4 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0509 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0510 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0511 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 hcq3 hcq4 h hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0512 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0513 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq3 h)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0514 A.natDegree B.natDegree C.natDegree E.natDegree hcq1 hcq3 h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0515 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0516 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 h hcq2 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0400 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0401 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0518 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos hcq1 hcq2 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0405 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0519 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq1 hcq2 hcq0)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq1 hcq3; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq2; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega)
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
/-- Chamber `BCEG` / `CG·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq3 hcq4 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0520 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0521 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq3 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0522 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAD h hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0523 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hAF hcq1 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0524 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0525 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAD h hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0526 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0527 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0528 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0529 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0530 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq3 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0531 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hAD hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0532 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hAF hcq1 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0533 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0534 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0535 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0536 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0537 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0538 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0539 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq3 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0540 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hAD hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0541 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hAF hcq1 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0542 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0543 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0544 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0545 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0546 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0547 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hAD hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0548 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0549 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0550 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0551 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq3 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0552 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0553 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq3 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0554 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0555 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0556 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0557 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0558 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0559 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hDn hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0560 A.natDegree B.natDegree C.natDegree G.natDegree hcq1 h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0561 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0562 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4 hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0563 A.natDegree B.natDegree C.natDegree G.natDegree h hcq4 hcq0)
  have hr0 : (kappaQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest10810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz (by clear * - hcq1; omega) hz0l hz0beta (Or.inr (by clear * - hcq1 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1; omega))
  have hct0 := kappaQuarticChamberFace10810_coeff_top hBne hCne hGne (A := A) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face10_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq3 hcq4 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0564 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0565 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0566 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0567 A.natDegree B.natDegree C.natDegree E.natDegree h hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0568 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0569 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0570 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0573 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0575 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0576 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0577 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq1 hcq3 hcq4 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0580 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq1 hDn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0582 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hFn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0583 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0584 A.natDegree B.natDegree C.natDegree hApos h hcq1)
  have hr1 : (muQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest7810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq1 hcq3; omega) (by clear * - hcq0 hcq2; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hct1 := muQuarticChamberFace7810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticChamberInnerSystem3810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc hGc

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
/-- Chamber `BCEG` / `CG·EE·CCC`: the faces of κ, μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCEG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG18810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq2 hcq3 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0585 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAD h hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0586 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0587 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAD h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0588 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0524 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0589 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAD h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0590 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAD h hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0591 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0592 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0593 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0594 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0595 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hAD hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0596 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0533 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0597 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0598 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0599 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0600 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0601 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0602 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0603 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hAD hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0604 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0542 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0605 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0606 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0607 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0608 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0609 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hAD hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0610 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0611 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0612 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hDn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0613 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0614 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0615 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0554 A.natDegree B.natDegree C.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0616 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0617 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0618 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0619 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0620 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0621 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 h hcq0 hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0622 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0623 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0624 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq0 hcq3 hcq1)
  have hr0 : (kappaQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest10810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz (by clear * - hcq2; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq2; omega))
  have hct0 := kappaQuarticChamberFace10810_coeff_top hBne hCne hGne (A := A) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face10_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq2 hcq3 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0564 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0565 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0625 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0567 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0626 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0627 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0628 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0629 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0630 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0631 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0632 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq2 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0633 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0634 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0635 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0636 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq0 hcq3 hcq1)
  have hr1 : (muQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest11810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by clear * - hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq2 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega))
  have hct1 := muQuarticChamberFace11810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 4 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hFn hcq0 hcq1 hcq2 hcq3 hApos hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ 5 * B.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + 3 * C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * E.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0637 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0638 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0625 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0639 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0626 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0640 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0641 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0642 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0643 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0629 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0644 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0630 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0645 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0646 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0647 A.natDegree B.natDegree C.natDegree hcq2 h)
      · exact Or.inr (astra4u_Round4Package_nat_0648 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0633 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 hDn hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0649 A.natDegree B.natDegree C.natDegree E.natDegree h hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0634 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq3 hFn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_0650 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0651 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq1)
  have hr2 : (piQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest4810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz hFz (by clear * - hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq2 hcq3; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega))
  have hct2 := piQuarticChamberFace4810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1 hdp2; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hDn hFn hdp0 hdp1 hdp2; omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face4_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticNoTargetInner_BCEG_zero_impossible B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hBc hCc hEc hGc

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
/-- Chamber `BCFG` / `BBB·BBC·BCC·CCC`: the faces of κ, μ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0157 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0137 A.natDegree B.natDegree E.natDegree F.natDegree hApos hAB hcq7 h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0002 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0138 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0004 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0005 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0006 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0007 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0652 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hAB h hcq0 hcq5 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0159 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0140 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0011 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0141 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0013 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0014 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0015 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0016 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0160 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0161 A.natDegree B.natDegree D.natDegree G.natDegree hApos hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0142 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hAB h hcq0 hcq5 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0020 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0143 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0022 A.natDegree B.natDegree C.natDegree E.natDegree hApos hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0023 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0024 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0025 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0026 A.natDegree B.natDegree E.natDegree hAB hAE h hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0027 A.natDegree B.natDegree C.natDegree D.natDegree hAB h hAD hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0028 A.natDegree B.natDegree hAB h)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0029 A.natDegree B.natDegree C.natDegree hApos h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0162 A.natDegree B.natDegree D.natDegree G.natDegree hAB h hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0144 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAB h hcq0 hcq5 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0032 A.natDegree B.natDegree D.natDegree hApos h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0145 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0034 A.natDegree B.natDegree C.natDegree E.natDegree hAB h hcq0 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0035 A.natDegree B.natDegree D.natDegree hApos hAB h hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0036 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0037 A.natDegree B.natDegree C.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0038 A.natDegree B.natDegree E.natDegree hApos hAB h hEn)
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
    · exact Or.inr (astra4u_Round4Package_nat_0147 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAB hcq0 hcq5 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0046 A.natDegree B.natDegree D.natDegree hApos h hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0148 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0048 A.natDegree B.natDegree C.natDegree E.natDegree hApos h hcq0 hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0049 A.natDegree B.natDegree D.natDegree hApos h hAB hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0050 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0051 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0052 A.natDegree B.natDegree E.natDegree hApos h hAB hEn)
    · exact Or.inr (astra4u_Round4Package_nat_0053 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hAB hcq0 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0149 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_0056 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0057 A.natDegree B.natDegree D.natDegree hApos h hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hEz (by clear * - hcq4; omega) (by clear * - hcq5; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0; omega)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0164 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0150 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0060 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0061 A.natDegree B.natDegree C.natDegree hAB h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0062 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0063 A.natDegree B.natDegree C.natDegree hAB h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0653 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hAB h hcq0 hcq5 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0166 A.natDegree B.natDegree C.natDegree G.natDegree hAB h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0152 A.natDegree B.natDegree C.natDegree F.natDegree hAB h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0067 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hAE h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0068 A.natDegree B.natDegree C.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_0069 A.natDegree B.natDegree C.natDegree D.natDegree hApos hAB h hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0070 A.natDegree B.natDegree C.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0153 A.natDegree B.natDegree C.natDegree F.natDegree h hAB hcq0 hcq5)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0167 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0154 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0074 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos h hcq0 hDn hEn)
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
    muQuarticChamberRest3810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hEz (by clear * - hAB hcq0; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq4 hcq5 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hct1 := muQuarticChamberFace3810_coeff_top hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdp1; omega)
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
/-- Chamber `BCFG` / `CG·CCC`: the faces of μ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBCFG28810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG28810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq5 hcq6 hApos hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0654 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0655 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0566 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0656 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0657 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0658 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0659 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq6 hcq0)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0573 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0660 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0661 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0576 A.natDegree B.natDegree C.natDegree G.natDegree h hcq2 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0662 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq0)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq2 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0580 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0663 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0664 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0583 A.natDegree B.natDegree C.natDegree G.natDegree h hcq2 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0665 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hApos h hcq2 hcq1 hcq0)
  have hr0 : (muQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest7810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hEz (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hz0delta (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace7810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0; omega)
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
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq5 hcq6 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ 5 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 4 * C.natDegree ∧ B.natDegree + 3 * C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 4 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0666 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0667 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0566 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0656 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0668 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0669 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0670 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq6 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0671 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0672 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0573 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0660 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0673 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0674 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0675 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq6 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 4 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0676 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq2 hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0677 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0580 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq2 hDn hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0663 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq2 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0678 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0679 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq2 hcq3 hcq6 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0680 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hApos h hcq2 hcq1 hcq0)
  have hr1 : (piQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest1810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hEz (by clear * - hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq1 hcq2 hcq6; omega) (by clear * - hcq0 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace1810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hApos hAB hAC hAD hAE hAF hAG hDn hEn hdp0 hdp1; omega)
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
/-- Chamber `BDEG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBDEG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
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
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0343 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0681 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq6 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0345 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0682 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hCn hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0683 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq6 h hCn hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0684 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq6 h hCn hcq3 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0685 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hcq3 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0350 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0686 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq6 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0352 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0687 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hCn hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0688 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq6 h hCn hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0689 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq6 h hCn hcq3 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0690 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hcq3 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0357 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0187 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq6 h hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0359 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hcq3 hFn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0190 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq5 hcq6 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0691 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hCn hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0193 A.natDegree B.natDegree C.natDegree G.natDegree hcq6 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0194 A.natDegree B.natDegree E.natDegree G.natDegree hcq5 hcq6 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0692 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq6 h hCn hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq6 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0693 A.natDegree B.natDegree E.natDegree G.natDegree hApos hcq5 hcq6 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0366 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0199 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq6 h hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0368 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hcq3 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0202 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq5 hcq6 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0694 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hCn hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0205 A.natDegree B.natDegree C.natDegree G.natDegree hcq6 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0206 A.natDegree B.natDegree E.natDegree G.natDegree hcq5 hcq6 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0695 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq6 h hCn hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq6 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0374 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 h hcq3 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0210 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq6 h hCn hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0377 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0500 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq6 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0379 A.natDegree B.natDegree F.natDegree G.natDegree h hcq6 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0213 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hApos h hcq4 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_0696 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq6 hCn hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0216 A.natDegree B.natDegree C.natDegree hApos h hCn)
    · exact Or.inr (astra4u_Round4Package_nat_0217 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0697 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq6 hCn hcq3 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0385 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq6 hcq3 hFn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0219 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq6 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0387 A.natDegree B.natDegree D.natDegree G.natDegree h hcq6 hcq3 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hFz (by clear * - hcq3; omega) (by clear * - hcq0 hcq2; omega) hz0l hz0beta hz0delta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq2 hcq3; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0; omega)
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
  have hz1l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0220 A.natDegree B.natDegree E.natDegree G.natDegree hcq5 hcq6 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0698 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0223 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0225 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq6 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0699 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq6 h hcq2 hcq3 hcq0)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0227 A.natDegree B.natDegree E.natDegree G.natDegree hApos h hcq4 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0700 A.natDegree B.natDegree D.natDegree E.natDegree hcq5 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0230 A.natDegree B.natDegree E.natDegree hcq5 h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0232 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0701 A.natDegree B.natDegree D.natDegree E.natDegree h hcq3)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hFz (by clear * - hcq3; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hFn hdp0 hdp1; omega)
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
/-- Chamber `BDFG` / `BG·BBB`: the faces of κ, π vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBDFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0343 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0702 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq4 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0082 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0247 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0703 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hAC hcq7 hAE h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0083 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0683 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq7 h hCn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0684 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq7 h hCn hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0704 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq4 hcq6 hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0350 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0705 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq4 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0087 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0253 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0706 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq7 hAE h hCn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0088 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0688 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq7 h hCn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0689 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq7 h hCn hcq4 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0707 A.natDegree B.natDegree D.natDegree G.natDegree hcq7 h hcq4 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0357 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0708 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq4 hEn hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0092 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0259 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0709 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq7 hAE h hCn hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0093 A.natDegree B.natDegree D.natDegree h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0710 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hCn hcq4 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0193 A.natDegree B.natDegree C.natDegree G.natDegree hcq7 h hCn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0363 A.natDegree B.natDegree E.natDegree G.natDegree hcq7 hAE h hEn hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0692 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq7 h hCn hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0196 A.natDegree B.natDegree G.natDegree hcq7 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0711 A.natDegree B.natDegree hApos h)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0366 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0712 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hEn hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0097 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0713 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0714 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq7 h hCn hcq4 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0098 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0715 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hCn hcq4 hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0205 A.natDegree B.natDegree C.natDegree G.natDegree hcq7 h hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0372 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq7 h hcq4 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0695 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hAC hcq7 h hCn hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0208 A.natDegree B.natDegree G.natDegree hcq7 h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0716 A.natDegree B.natDegree F.natDegree G.natDegree hcq7 h hcq6 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0210 A.natDegree B.natDegree C.natDegree G.natDegree hAC hcq7 h hCn hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0377 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0278 A.natDegree B.natDegree E.natDegree F.natDegree h hEn hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0102 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0717 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0718 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq7 hCn hcq4 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0103 A.natDegree B.natDegree D.natDegree h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0696 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq7 hCn hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0216 A.natDegree B.natDegree C.natDegree hApos h hCn)
    · exact Or.inr (astra4u_Round4Package_nat_0383 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq7 hcq4 hEn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0697 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq7 hCn hcq4 hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0054 A.natDegree B.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_0286 A.natDegree B.natDegree F.natDegree h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_0219 A.natDegree B.natDegree C.natDegree G.natDegree hApos h hcq7 hCn hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_0387 A.natDegree B.natDegree D.natDegree G.natDegree h hcq7 hcq4 hcq0)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hEz (by clear * - hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hEn hdp0; omega)
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
  have hz1l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0719 A.natDegree B.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0720 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq4 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0721 A.natDegree B.natDegree F.natDegree G.natDegree h hcq7 hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0722 A.natDegree B.natDegree F.natDegree G.natDegree h hcq7 hcq6 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0723 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq4 hcq6 hcq0)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0724 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0725 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq4 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0726 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0727 A.natDegree B.natDegree F.natDegree G.natDegree h hcq7 hcq6 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0728 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq1 hcq4 hcq0)
  have hz1delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0729 A.natDegree B.natDegree F.natDegree G.natDegree hcq1 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0731 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq4 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_0732 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_0733 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0734 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq4)
  have hr1 : (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest3810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hEz (by clear * - hcq4; omega) (by clear * - hcq6; omega) (by clear * - hcq4; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hct1 := piQuarticChamberFace3810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hEn hdp0 hdp1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hEn hdp0 hdp1; omega)
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
/-- Chamber `BEFG` / `BF·BG·EE·BBB`: the faces of κ, ξ vanish, and the isobaric certificate then kills it. -/
theorem quarticChamberBEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
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
      · exact Or.inr (astra4u_Round4Package_nat_0735 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq2 hAD h hcq0 hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0736 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0737 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 hAD h hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0738 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0739 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAC hcq3 hcq2 h hcq1 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0740 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 hAD h hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0741 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 hAD h hcq1 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0742 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAC hcq3 hcq2 h hcq1 hCn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0743 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0744 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq2 hAD h hcq0 hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0745 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0746 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hAD hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0747 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0748 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAC hcq3 hcq2 h hcq1 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0749 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0750 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 hAD h hcq1 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0751 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hAC hcq3 hcq2 h hcq1 hCn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0752 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0753 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq2 h hAD hcq0 hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0754 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0755 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hAD hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0756 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0757 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0758 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hcq1 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0759 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hAD hcq1 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0760 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0761 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0762 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hAD hcq1 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0763 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0764 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0765 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0766 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0767 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0768 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0769 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hCn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0770 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hcq1 hDn)
    · exact Or.inr (astra4u_Round4Package_nat_0771 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hAD hcq1 hCn)
    · exact Or.inr (astra4u_Round4Package_nat_0772 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hCn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0773 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0774 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq2 h hAD hcq1 hCn)
    · exact Or.inr (astra4u_Round4Package_nat_0775 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq1 h hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0776 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0777 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAC hcq2 h hcq0 hcq1 hCn hcq4)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0778 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0779 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0780 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq1 h hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0781 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0782 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hCn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0783 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0784 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hCn hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0785 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hCn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0786 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0787 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hCn hDn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0788 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0789 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0790 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAC h hcq2 hcq0 hcq1 hCn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_0791 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hDn hcq4)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hDz hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) hz0theta
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
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0792 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0793 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq1 hCn hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0794 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq1 hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0795 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0796 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0797 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0798 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq4)
  have hz1beta : beta = 0 ∨ (A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0799 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0800 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq1 hCn hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0801 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq0 hcq1 hDn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0802 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0803 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0804 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_0805 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hcq4)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hDz (by clear * - hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq2 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega))
  have hct1 := xiQuarticChamberFace19810_coeff_top hAne hBne hEne hGne (C := C) (D := D) (F := F) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hDn hdp0 hdp1; omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticChamberInner19810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticChamberInnerSystem6810_zero_impossible A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hEc hFc hGc

end QuarticChamberKills4810

end Max11DegreeRoutes
