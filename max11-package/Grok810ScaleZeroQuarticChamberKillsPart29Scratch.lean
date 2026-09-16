import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart06Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart07Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart08Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart09Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart10Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart11Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart12Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart14Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
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
/-- Chamber `BCDEF` / `BF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1713 A.natDegree B.natDegree C.natDegree F.natDegree hcq3 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1348 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2029 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq7 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2859 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq4 h hcq7 hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1351 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1715 A.natDegree B.natDegree C.natDegree F.natDegree hcq3 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1352 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2031 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq7 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2860 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq3 hcq4 h hcq7 hcq1 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq3 hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1713 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2034 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1818 A.natDegree B.natDegree E.natDegree F.natDegree h hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1819 A.natDegree B.natDegree E.natDegree F.natDegree h hcq5 hcq7 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2035 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq7 hcq0 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2861 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq5 h hcq7 hcq0 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1822 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1715 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2038 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1824 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1825 A.natDegree B.natDegree E.natDegree F.natDegree h hcq5 hcq7 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2039 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq7 hcq0 hcq4 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2862 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq5 h hcq7 hcq0 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1828 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1829 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2042 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1831 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1832 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 h hcq7 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2043 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq7 hcq0 hcq4 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2863 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq5 hcq7 hcq0 hcq4)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq5 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq1 hcq5 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq5 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq2 hcq4 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEF24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1404 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1835 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq3 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2045 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1405 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1406 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2864 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq1 h hcq0 hcq10 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1408 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1837 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq3 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2047 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1409 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1410 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2865 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq3 hcq1 hcq0 hcq10 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq10; omega) (by clear * - hcq1 hcq6 hcq10; omega) (by clear * - hcq1 hcq3 hcq10; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq1 hcq3 hcq10; omega) (by clear * - hcq0 hcq1 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1412 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2866 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq1 hcq5 h hcq7 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1414 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 hcq5 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2867 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq0 hcq1 hcq5 h hcq7 hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq4; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCDEF26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hGn hcq0 hcq7 hcq8 hApos hcq15 hcq16 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1719 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq8 hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1720 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq8 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1721 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq8 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2868 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAC hcq8 hcq2 hcq1 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1722 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq2 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2869 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hAC h hcq8 hcq2 hcq16)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1190 A.natDegree B.natDegree C.natDegree D.natDegree hAC h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq8 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1245 A.natDegree B.natDegree C.natDegree F.natDegree h hAC hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2870 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq8 hcq2 hcq1 hcq16)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq8 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1192 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq8 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1247 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1070 A.natDegree G.natDegree hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1725 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq8 hcq2 hcq0)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq8; omega) (by clear * - hAC hcq8; omega) (by clear * - hcq0; omega) (by clear * - hcq2; omega) (by clear * - hcq8 hcq16; omega) (by clear * - hAC hcq2 hcq8; omega) (by clear * - hAC hcq1 hcq2; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq2 hcq8 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCDEF28810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF28810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq4 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1726 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1727 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1728 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2871 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq12 hcq15 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1729 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq12 hcq15)
      · exact absurd h (astra4u_Round4Package_nat_1254 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq7 hcq12 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2872 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1256 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1257 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1731 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1846 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq12 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1260 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7 hcq0 hcq12)
      · exact absurd h (astra4u_Round4Package_nat_1261 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq7 hcq12 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2873 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq2 hcq12 hcq15 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1263 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1264 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1733 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1848 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq12 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1267 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact absurd h (astra4u_Round4Package_nat_1268 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq7 hcq12 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1734 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq2 hcq12 hcq15)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq7 hcq12; omega) (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq6 hcq12; omega) (by clear * - hcq0 hcq12 hcq15; omega) (by clear * - hcq0 hcq15; omega) (by clear * - hcq0 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hApos hcq12 hcq15; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq6 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hApos hcq12 hcq15; omega)) (Or.inr (by clear * - hcq0 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hApos hcq12; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEF29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF29810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1735 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1736 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq14 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1737 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq14 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2874 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq3 hcq14 hcq11 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1739 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq14 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1740 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq3 hcq14 hcq1 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2875 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq14 hcq1 hcq11 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1742 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1743 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1744 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2876 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq11 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1746 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1747 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq3 hcq14 hcq1 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2877 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq14 hcq11 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1749 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq1 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1750 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1751 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2878 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq11 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1753 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1754 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq3 hcq14 hcq1 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2539 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq1 hcq11)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq11; omega) (by clear * - hcq0 hcq3 hcq11; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2879 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq6 hcq2 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2205 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2206 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2207 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq2 hcq15 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2208 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq15)
      · exact absurd h (astra4u_Round4Package_nat_2880 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq2 hcq15 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2881 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq6 hcq2 hcq15 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq0 hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq1 hcq2 hcq6 hcq15; omega) (by clear * - hcq0 hcq2 hcq15; omega) (by clear * - hcq0 hcq6 hcq15; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq15; omega) (by clear * - hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq15; omega) (by clear * - hcq0 hcq1 hcq6 hcq15; omega) (by clear * - hcq15; omega) (by clear * - hcq0 hcq1 hcq2 hcq15; omega) (by clear * - hcq1 hcq15; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·DD·DE·EE` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF32810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF32810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2882 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2216 A.natDegree C.natDegree D.natDegree F.natDegree hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_2217 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2218 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2219 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2220 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq1 hcq5 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2883 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq14 hcq3 hcq11 hcq1 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2884 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2223 A.natDegree C.natDegree D.natDegree F.natDegree hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_2224 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2225 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2226 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2227 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq1 hcq5 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2885 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq14 hcq3 hcq11 hcq1 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2886 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq3 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2230 A.natDegree C.natDegree D.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2231 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2232 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2233 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2234 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq1 hcq5 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2887 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq3 hcq11 hcq1 hcq5)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq3 hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega) (by clear * - hcq1 hcq5 hcq11; omega) (by clear * - hcq1 hcq5 hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq1 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEF35810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF35810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2888 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2889 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2890 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2891 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2892 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1543 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq0 hcq5 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2893 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1854 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1855 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2894 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1856 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1857 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1550 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq0 hcq5 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2895 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1859 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 hcq0 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1860 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2896 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1862 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1863 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1864 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq1 hcq0 hcq5 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2897 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11 hcq3 hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq3 hcq5 hcq11; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEF37810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF37810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq3 hcq4 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1866 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq3 hcq0 hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1551 A.natDegree C.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2245 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1552 A.natDegree C.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1553 A.natDegree C.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2898 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq3 hcq0 hcq1 hcq11 hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq3 hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq0 hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq1 hcq5; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEF38810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF38810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq2 hcq5 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1270 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1147 A.natDegree C.natDegree F.natDegree hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_1519 A.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_1558 A.natDegree C.natDegree E.natDegree F.natDegree h hcq14 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1148 A.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2899 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hcq0 h hcq14 hcq1 hcq11 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq6 hcq11; omega) (by clear * - hcq0 hcq4 hcq11; omega) (by clear * - hcq1 hcq4 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq4 hcq6 hcq11; omega) (by clear * - hcq0 hcq6 hcq14; omega) (by clear * - hcq0 hcq4 hcq14; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi

end QuarticChamberKills810

end Max11DegreeRoutes
