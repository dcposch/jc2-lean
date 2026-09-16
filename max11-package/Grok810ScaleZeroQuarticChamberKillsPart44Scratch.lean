import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart06Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart07Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart08Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart09Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart10Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart11Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart12Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart13Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart14Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart101Scratch

/-! # Single-monomial chamber kills, `(8,10)` scale zero

11 face-degree lemmas and 550 chamber kills: every leaf whose
level-0 certificate is a single monomial *and* whose eight load columns
are either empty, dominated by the chamber's own ℕ conjuncts, or covered
by the κ band of `…ChamberBandsScratch`.  Which leaves those are is
decided, with exact rational Farkas certificates, by
`scripts/derive_810_quartic_chamber_killplan.py`; the rest are named in
the residual.  Untracked working note.
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

section QuarticChamberKills810

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEFG45810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG45810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1713 A.natDegree B.natDegree C.natDegree F.natDegree hcq4 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1348 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2029 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq13 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2127 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hcq13 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2942 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq6 hcq3 h hcq13 hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1351 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1715 A.natDegree B.natDegree C.natDegree F.natDegree hcq4 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1352 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2031 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq13 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_2129 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hcq13 hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2860 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq4 hcq6 h hcq13 hcq1 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq1 hcq13; omega) (by clear * - hcq4 hcq13; omega) (by clear * - hcq0 hcq1 hcq4 hcq13; omega) (by clear * - hcq3 hcq13; omega) (by clear * - hcq4 hcq13; omega) (by clear * - hcq6 hcq13; omega) (by clear * - hcq0 hcq4 hcq13; omega) (by clear * - hcq0 hcq1 hcq13; omega) (by clear * - hcq0 hcq1 hcq4 hcq6 hcq13; omega) (by clear * - hcq1 hcq13; omega) (by clear * - hcq1 hcq4 hcq13; omega) (by clear * - hcq4 hcq13; omega) (by clear * - hcq1 hcq3 hcq13; omega) (by clear * - hcq0 hcq1 hcq6 hcq13; omega) (by clear * - hcq3 hcq4 hcq13; omega) (by clear * - hcq1 hcq4 hcq13; omega) (by clear * - hcq0 hcq4 hcq6 hcq13; omega) (by clear * - hcq1 hcq6 hcq13; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEFG46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG46810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1713 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_2034 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1818 A.natDegree B.natDegree E.natDegree F.natDegree h hcq8 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1819 A.natDegree B.natDegree E.natDegree F.natDegree h hcq8 hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2157 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq1 hcq13 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2943 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq8 hcq1 h hcq13 hcq0 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1822 A.natDegree B.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1715 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_2038 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1824 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1825 A.natDegree B.natDegree E.natDegree F.natDegree h hcq8 hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2159 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq1 hcq13 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2862 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq8 h hcq13 hcq0 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1828 A.natDegree B.natDegree F.natDegree hcq13 h)
      · exact Or.inr (astra4u_Round4Package_nat_1829 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_2042 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1831 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1832 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2161 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq1 hcq13 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2863 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq8 hcq13 hcq0 hcq6)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq6 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq0 hcq2 hcq8 hcq13; omega) (by clear * - hcq1 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq0 hcq4 hcq13; omega) (by clear * - hcq2 hcq4 hcq13; omega) (by clear * - hcq0 hcq8 hcq13; omega) (by clear * - hcq2 hcq8 hcq13; omega) (by clear * - hcq6 hcq13; omega) (by clear * - hcq2 hcq6 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq1 hcq6 hcq13; omega) (by clear * - hcq8 hcq13; omega) (by clear * - hcq1 hcq2 hcq13; omega) (by clear * - hcq2 hcq6 hcq13; omega) (by clear * - hcq0 hcq2 hcq13; omega) (by clear * - hcq0 hcq4 hcq6 hcq13; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6 hcq8 hApos hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq2 hcq4 hcq6 hcq8 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq8 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8 hApos hcq13; omega)) (Or.inr (by clear * - hcq2 hApos hcq13; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEFG48810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG48810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1404 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1835 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq1 h hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_2045 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq16 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1405 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1406 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_2163 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq16 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2944 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq1 h hcq0 hcq16 hcq8 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1408 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1837 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq1 h hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_2047 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq16 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1409 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1410 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_2164 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq16 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2865 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq1 hcq0 hcq16 hcq8)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq16; omega) (by clear * - hcq0 hcq1 hcq16; omega) (by clear * - hcq0 hcq1 hcq4 hcq8 hcq16; omega) (by clear * - hcq1 hcq8 hcq16; omega) (by clear * - hcq1 hcq4 hcq16; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq1 hcq10 hcq16; omega) (by clear * - hcq1 hcq4 hcq16; omega) (by clear * - hcq0 hcq1 hcq8 hcq16; omega) (by clear * - hcq0 hcq1 hcq4 hcq16; omega) (by clear * - hcq0 hcq1 hcq4 hcq8 hcq16; omega) (by clear * - hcq0 hcq1 hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hApos hcq16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hApos hcq16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG49810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG49810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1412 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq8 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1474 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2945 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq2 hcq8 hcq1 h hcq13 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1414 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 hcq8 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1476 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq13)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2867 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq0 hcq2 hcq8 h hcq13 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq2 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq8 hcq13; omega) (by clear * - hcq2 hcq6 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq6; omega) (by clear * - hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG52810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG52810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq3 hcq6 hcq7 hcq10 hcq12 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1273 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1274 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1762 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq13 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1887 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq9 hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1946 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq12 hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1278 A.natDegree B.natDegree C.natDegree G.natDegree h hcq12 hcq13 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2946 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq9 hcq12 h hcq13 hcq0 hcq2 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1280 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1281 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1764 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq13 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1889 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq9 h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1948 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq12 hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1285 A.natDegree B.natDegree C.natDegree G.natDegree h hcq12 hcq13 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2947 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq9 hcq12 h hcq13 hcq0 hcq2 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1287 A.natDegree B.natDegree C.natDegree G.natDegree hcq13 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1288 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1766 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq13 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1891 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq9 h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1950 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq12 h hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1292 A.natDegree B.natDegree C.natDegree G.natDegree h hcq12 hcq13 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2504 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq12 hcq13 hcq0 hcq2 hcq6)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq0 hcq12 hcq13; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq9 hcq13; omega) (by clear * - hcq6 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq6 hApos hcq12 hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq9 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq12 hcq13; omega)) (Or.inr (by clear * - hcq12 hcq13; omega)) (Or.inr (by clear * - hcq0 hApos hcq13; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG56810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG56810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq7 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2948 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2071 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq3 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2072 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq13 hcq3 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2949 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq3 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2073 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq13 hcq3 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2950 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq3 hcq2 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2951 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2076 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq3 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2077 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq3 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2952 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq3 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2078 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq13 hcq3 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2953 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq3 hcq2 hcq8)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq2 hcq3 hcq13; omega) (by clear * - hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq13; omega) (by clear * - hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq2 hcq3 hcq13; omega) (by clear * - hcq2 hcq3 hcq8 hcq13; omega) (by clear * - hcq3 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq2 hcq3 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq3 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·DD·DE·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG57810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG57810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq7 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2948 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2080 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2081 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq13 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2954 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq2 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2082 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq13 hcq2 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2955 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2 hcq5 hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2951 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2084 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2085 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2956 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq2 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2086 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq13 hcq2 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2957 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2 hcq5 hcq7)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2088 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq13 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2958 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2089 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2090 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq13 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2959 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq13 hcq0 hcq2 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2091 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq13 hcq2 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2960 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq2 hcq5 hcq7)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq2 hcq7 hcq13; omega) (by clear * - hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq13; omega) (by clear * - hcq2 hcq7 hcq13; omega) (by clear * - hcq0 hcq2 hcq7 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq5; omega) (by clear * - hcq2 hcq7 hcq13; omega) (by clear * - hcq2 hcq5 hcq7 hcq13; omega) (by clear * - hcq7 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq13; omega) (by clear * - hcq0 hcq2 hcq5 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hcq13; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq7 hcq13; omega)) (Or.inr (by clear * - hcq2 hcq7 hcq13; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·DD·DG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEFG59810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG59810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2505 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2506 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2507 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq13 hcq0 hcq2 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2961 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq2 hcq5 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2508 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq2 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2509 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq2 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2962 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq13 hcq0 hcq2 hcq6)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq13; omega) (by clear * - hcq13; omega) (by clear * - hcq5 hcq13; omega) (by clear * - hcq6 hcq13; omega) (by clear * - hcq0 hcq1 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq5 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq0 hcq2 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq5 hcq6 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq2 hcq5 hcq13; omega) (by clear * - hcq0 hcq1 hcq6 hcq13; omega) (by clear * - hcq2 hcq6 hcq13; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG62810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG62810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2963 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq1 hcq13 hcq0 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2964 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq1 hcq13 hcq0 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2965 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq1 hcq13 hcq0 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2966 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq13 hcq0 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2967 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq13 hcq0 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2968 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq13 hcq0 hcq5 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2969 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq2 h hcq1 hcq13 hcq0 hcq7)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq2 hcq13; omega) (by clear * - hcq13; omega) (by clear * - hcq0 hcq1 hcq7 hcq13; omega) (by clear * - hcq1 hcq2 hcq7 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq13; omega) (by clear * - hcq0 hcq1 hcq5 hcq7; omega) (by clear * - hcq1 hcq2 hcq13; omega) (by clear * - hcq1 hcq2 hcq5 hcq13; omega) (by clear * - hcq1 hcq2 hcq7 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq5; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq2 hcq7 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG63810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG63810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1273 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1274 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1762 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq13 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1887 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq10 hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1952 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1294 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq13 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2970 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq10 h hcq1 hcq13 hcq0 hcq3 hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1280 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1281 A.natDegree B.natDegree C.natDegree G.natDegree h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1764 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq13 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1889 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq10 h hcq13 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1954 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1296 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq13 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2971 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq10 h hcq1 hcq13 hcq0 hcq3 hcq7)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq0 hcq1 hcq13; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq10 hcq13; omega) (by clear * - hcq7 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEFG64810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG64810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1770 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq3 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1368 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2065 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq13 hcq4 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2131 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1371 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq13 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2972 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq3 h hcq13 hcq1 hcq2 hcq4 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1772 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq3 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1375 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2067 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq13 hcq4 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2133 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1378 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq13 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2973 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq3 h hcq13 hcq1 hcq4 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1380 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 hcq13 h)
      · exact Or.inr (astra4u_Round4Package_nat_1774 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq3 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1382 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2069 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq13 hcq4 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2135 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq13 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1385 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq13 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2515 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq13 hcq1 hcq6)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq3 hcq13; omega) (by clear * - hcq0 hcq6 hcq13; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq4 hcq6 hcq13; omega) (by clear * - hcq0 hcq3 hcq6 hcq13; omega) (by clear * - hcq0 hcq3 hcq13; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq13; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG66810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG66810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq6 hcq8 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq13 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2384 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq8 h hcq13 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2071 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq13 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2072 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2693 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2073 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2974 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq8 h hcq13 hcq2 hcq1 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq13 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2386 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq8 h hcq13 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2076 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq13 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2077 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq13 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2695 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2078 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2975 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq8 h hcq13 hcq2 hcq1 hcq10)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq2 hcq13; omega) (by clear * - hcq13; omega) (by clear * - hcq0 hcq1 hcq8 hcq13; omega) (by clear * - hcq1 hcq2 hcq13; omega) (by clear * - hcq1 hcq2 hcq8 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq1 hcq2 hcq13; omega) (by clear * - hcq0 hcq1 hcq8 hcq10 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq8 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq8 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos hcq10 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos hcq10 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi

end QuarticChamberKills810

end Max11DegreeRoutes
