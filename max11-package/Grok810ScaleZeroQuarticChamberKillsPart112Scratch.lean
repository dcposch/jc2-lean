import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart06Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart07Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart08Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart09Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart10Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart11Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart13Scratch
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
/-- Chamber `BDEFG` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBDEFG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_2685 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq6 hcq11 hcq0 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2034 A.natDegree B.natDegree D.natDegree F.natDegree h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1818 A.natDegree B.natDegree E.natDegree F.natDegree h hcq6 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1819 A.natDegree B.natDegree E.natDegree F.natDegree h hcq6 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2157 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq6 hcq1 hcq11 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2686 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hcq11 hcq0 hcq4)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1822 A.natDegree B.natDegree F.natDegree h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_2687 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq6 hcq11 hcq0 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2038 A.natDegree B.natDegree D.natDegree F.natDegree h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1824 A.natDegree B.natDegree E.natDegree F.natDegree hcq6 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1825 A.natDegree B.natDegree E.natDegree F.natDegree h hcq6 hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2159 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq6 hcq1 hcq11 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2040 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq11 hcq0 hcq4)
  have hbdelta' : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1828 A.natDegree B.natDegree F.natDegree hcq11 h)
      · exact absurd h (astra4u_Round4Package_nat_2688 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq6 hcq11 hcq0 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2042 A.natDegree B.natDegree D.natDegree F.natDegree h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1831 A.natDegree B.natDegree E.natDegree F.natDegree hcq6 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1832 A.natDegree B.natDegree E.natDegree F.natDegree hcq6 h hcq11 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2161 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq6 hcq1 hcq11 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2044 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq11 hcq0 hcq4)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq11; omega) (by clear * - hcq4 hcq11; omega) (by clear * - hcq1 hcq11; omega) (by clear * - hcq0 hcq2 hcq11; omega) (by clear * - hcq0 hcq6 hcq11; omega) (by clear * - hcq4 hcq11; omega) (by clear * - hcq1 hcq4 hcq11; omega) (by clear * - hcq6 hcq11; omega) (by clear * - hcq0 hcq2 hcq4 hcq11; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6 hApos hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq2 hcq4 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hApos hcq11; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBDEFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq3 hcq4 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1404 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq13)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2045 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1405 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1406 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_2163 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq13 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2689 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq13 hcq6 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1408 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq13)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2047 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq13 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1409 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1410 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_2164 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq13 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2048 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq13 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq1 hcq13; omega) (by clear * - hcq0 hcq1 hcq13; omega) (by clear * - hcq1 hcq6 hcq13; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq1 hcq8 hcq13; omega) (by clear * - hcq0 hcq1 hcq6 hcq13; omega) (by clear * - hcq0 hcq1 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBDEFG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1412 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq6 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1474 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq11)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2690 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq1 h hcq11 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1414 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 hcq6 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1476 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq11)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2050 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos hcq0 hcq6 h hcq11 hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq6 hcq11; omega) (by clear * - hcq4; omega) (by clear * - hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEFG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG27810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1367 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq11 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1368 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2065 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2131 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1371 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq11 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2691 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq2 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1374 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq11 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1375 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2067 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2133 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1378 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq11 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2692 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq2 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1380 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 hcq11 h)
      · exact absurd h (astra4u_Round4Package_nat_1381 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq11 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1382 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2069 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2135 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1385 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq11 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2136 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq4)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq4 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq2 hcq4 hcq11; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq4 hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq11; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBDEFG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG29810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq6 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2071 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2072 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2693 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq2 hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2073 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq2 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2694 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq2 hcq1 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2076 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2077 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2695 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq2 hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2078 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq2 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2696 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq2 hcq1 hcq8)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq1 hcq2 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq1 hcq2 hcq11; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq1 hcq2 hcq11; omega) (by clear * - hcq2 hcq11; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·DD·DE·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBDEFG30810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG30810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq3 hcq4 hcq5 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1367 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq11 hCn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2080 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2081 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2697 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq3 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2082 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq1 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2698 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq3 hcq1 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1374 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq11 hCn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2084 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2085 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2699 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq3 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2086 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq1 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2700 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq3 hcq1 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2088 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq11 h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1381 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq11 hCn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2089 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2090 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2701 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq3 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2091 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq1 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2702 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq3 hcq1 hcq5)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq1 hcq5 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq1 hcq5 hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq1 hcq3 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq11; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEFG32810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG32810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1387 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2093 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq11 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2137 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1388 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq11 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2703 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq4 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1390 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq11 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2095 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2139 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1391 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq11 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2704 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq1 hcq4 hcq10)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq4 hcq11; omega) (by clear * - hcq1 hcq10; omega) (by clear * - hcq0 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEFG33810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG33810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq2 hcq5 hcq6 hcq7 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1430 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq7 hcq0 hcq11 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2097 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq7 h hcq0 hcq11 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1432 A.natDegree B.natDegree E.natDegree G.natDegree h hcq7 hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2166 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0 hcq11 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1434 A.natDegree B.natDegree E.natDegree G.natDegree h hcq7 hcq0 hcq11)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2705 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq0 hcq11 hcq3 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1437 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq7 hcq0 hcq11 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2099 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq7 h hcq0 hcq11 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1439 A.natDegree B.natDegree E.natDegree G.natDegree hcq7 h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2168 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0 hcq11 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1441 A.natDegree B.natDegree E.natDegree G.natDegree h hcq7 hcq0 hcq11)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2706 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq0 hcq11 hcq3 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1443 A.natDegree B.natDegree E.natDegree G.natDegree hcq0 hcq11 h)
      · exact absurd h (astra4u_Round4Package_nat_1444 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq7 hcq0 hcq11 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2101 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq7 h hcq0 hcq11 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1446 A.natDegree B.natDegree E.natDegree G.natDegree hcq7 h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2170 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq0 hcq11 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1448 A.natDegree B.natDegree E.natDegree G.natDegree h hcq7 hcq0 hcq11)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2707 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0 hcq3 hcq6)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq7 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq7 hcq11; omega) (by clear * - hcq0 hcq3 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq7 hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq7 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7 hcq11; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEFG35810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG35810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq3 hcq4 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2103 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq11 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1449 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2172 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq11 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1450 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq11)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2708 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq11 hcq5 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2105 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq11 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1452 A.natDegree B.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2174 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq11 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1453 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq11)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2709 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq11 hcq5 hcq8)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq0 hcq5 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBDEFG36810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG36810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq6 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1477 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2141 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq11 hcq5 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2176 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq0 hcq11 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1478 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1479 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq11 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2710 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq8 h hcq0 hcq11 hcq5)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq5 hcq8 hcq11; omega) (by clear * - hcq10 hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq0 hcq10; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq0 hcq8 hcq10 hcq11; omega) (by clear * - hcq0 hcq5 hcq8 hcq11; omega) hbl' (Or.inr (by clear * - hcq0 hcq5 hcq8 hApos hcq10 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq8 hApos hcq10 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq8 hApos hcq10 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq8 hApos hcq10 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos hcq10; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEFG37810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG37810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1357 A.natDegree B.natDegree D.natDegree hcq12 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1358 A.natDegree B.natDegree D.natDegree hAB hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_2051 A.natDegree B.natDegree D.natDegree E.natDegree h hcq2 hAB hAD)
      · exact Or.inr (astra4u_Round4Package_nat_1359 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hAD hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2143 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hAB hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2711 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq4 h hAB hcq12 hAD hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1084 A.natDegree B.natDegree D.natDegree h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1085 A.natDegree B.natDegree D.natDegree hApos h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1330 A.natDegree B.natDegree D.natDegree E.natDegree hcq2 hAB h)
      · exact Or.inr (astra4u_Round4Package_nat_1361 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1395 A.natDegree B.natDegree D.natDegree G.natDegree h hcq4 hAB)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2053 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos hcq2 h hcq11 hcq3)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1087 A.natDegree B.natDegree D.natDegree hcq11 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1088 A.natDegree B.natDegree D.natDegree hApos h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1332 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq2 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1363 A.natDegree B.natDegree D.natDegree F.natDegree hAB h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1396 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1364 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq0)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq12; omega) (by clear * - hcq0; omega) (by clear * - hcq2 hcq12; omega) (by clear * - hcq3; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hApos hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos hcq11; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBDEFG40810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG40810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2054 A.natDegree B.natDegree D.natDegree F.natDegree hAD h hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1591 A.natDegree D.natDegree F.natDegree hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1592 A.natDegree D.natDegree E.natDegree F.natDegree h hAD hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1593 A.natDegree D.natDegree F.natDegree h hAD hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2372 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2712 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq5 hcq8)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq8; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq8; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq8; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi

end QuarticChamberKills810

end Max11DegreeRoutes
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
/-- Chamber `BDEFG` / `DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBDEFG41810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG41810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hCn hcq0 hcq1 hcq6 hcq7 hApos hcq11 hcq12 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2108 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq6 hcq1 hAD h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1614 A.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1615 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2376 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1616 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2713 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq1 h hAD hcq0 hcq7)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAD hcq0 hcq1 hcq6; omega) (by clear * - hAD hcq1 hcq6; omega) (by clear * - hAD hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hAD hcq0 hcq1 hcq6; omega) (by clear * - hAD hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq7; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEFG46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG46810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1397 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 hcq0 hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1054 A.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hAD hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2714 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq0 h hAD hcq8 hcq5)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAD hcq0 hcq3; omega) (by clear * - hcq0 hcq3 hcq5; omega) (by clear * - hAD hcq0 hcq3 hcq8; omega) (by clear * - hcq5; omega) (by clear * - hcq0 hcq8; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq3 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEFG47810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG47810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hcq0 hcq2 hcq6 hcq7 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2056 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq11 hAE h hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2057 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq13 hAE h hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2058 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq13 hcq6 hAE hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2059 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hAE hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2715 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq13 hcq6 hAE hcq2 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2716 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq13 hAE h hcq2 hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1093 A.natDegree B.natDegree E.natDegree hcq11 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1337 A.natDegree B.natDegree D.natDegree E.natDegree hcq13 hAE h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1094 A.natDegree B.natDegree E.natDegree hApos hcq13 h)
      · exact Or.inr (astra4u_Round4Package_nat_1420 A.natDegree B.natDegree E.natDegree F.natDegree h hcq6 hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1457 A.natDegree B.natDegree E.natDegree G.natDegree h hcq13 hAE hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2061 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos hcq13 h hcq2 hcq0)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1096 A.natDegree B.natDegree E.natDegree hcq11 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1339 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq13 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1097 A.natDegree B.natDegree E.natDegree hApos hcq13 h)
      · exact Or.inr (astra4u_Round4Package_nat_1422 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1458 A.natDegree B.natDegree E.natDegree G.natDegree h hcq13 hAE hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2062 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq2 hcq0)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq13; omega) (by clear * - hcq0; omega) (by clear * - hcq2; omega) (by clear * - hcq13; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq2 hcq7 hApos hcq11; omega)) hbdelta' (Or.inr (by clear * - hApos hcq11 hcq13; omega)) (Or.inr (by clear * - hcq2 hApos hcq11 hcq13; omega)) (Or.inr (by clear * - hApos hcq11; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `EE·EF·EG·FF·FG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEFG49810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG49810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hcq0 hcq1 hcq5 hcq7 hApos hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1424 A.natDegree B.natDegree E.natDegree F.natDegree hAE h hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1608 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2180 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2717 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq5 hcq1 hcq9)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAE hcq0 hcq5; omega) (by clear * - hcq5; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hAE hcq0 hcq5; omega) (by clear * - hcq9; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEFG50810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG50810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hcq0 hcq2 hcq4 hcq8 hApos hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1424 A.natDegree B.natDegree E.natDegree F.natDegree hAE h hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1608 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2182 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2718 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq2 hcq6 hcq8)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq6; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEFG51810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG51810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hcq0 hcq2 hcq3 hcq4 hcq8 hApos hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2719 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq3 hcq4 hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2720 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq3 hcq4 hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2721 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hAE hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2059 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hAE hcq4 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2722 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hAE hcq3 hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2723 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq3 hcq4 hcq0)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAE hcq0 hcq3; omega) (by clear * - hcq2; omega) (by clear * - hcq4; omega) (by clear * - hAE hcq0 hcq3; omega) (by clear * - hcq6; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBDEFG52810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG52810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hAE hCn hcq0 hcq2 hcq6 hcq9 hApos hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq0 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1175 A.natDegree E.natDegree F.natDegree h hAF hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq9 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2724 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq9 h hAF hcq6 hcq2)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAF hcq0; omega) (by clear * - hAF hcq0 hcq6; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hcq2; omega) (by clear * - hAF hcq0 hcq9; omega) (by clear * - hAF hcq0 hcq2 hcq6; omega) (by clear * - hcq8; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBDEFG53810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG53810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hAE hCn hcq0 hcq2 hcq4 hcq8 hApos hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq2 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1631 A.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2725 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hAF hcq0 hcq4 hcq10)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAF hcq2; omega) (by clear * - hAF hcq0 hcq2 hcq10; omega) (by clear * - hAF hcq2 hcq4; omega) (by clear * - hcq4; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hAF hcq0 hcq2 hcq4 hcq10; omega) (by clear * - hcq10; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hcq4 hApos hcq10; omega)) (Or.inr (by clear * - hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq4 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos hcq10; omega)) (Or.inr (by clear * - hcq2 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBDEFG54810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG54810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hAE hAF hCn hcq1 hcq2 hcq6 hcq9 hApos hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1483 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 hAG hcq1 h)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1627 A.natDegree D.natDegree F.natDegree G.natDegree hcq4 hcq2 hAG h)
      · exact Or.inr (astra4u_Round4Package_nat_1636 A.natDegree E.natDegree F.natDegree G.natDegree h hAG hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2726 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq2 h hAG hcq1 hcq6)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq2; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq2 hcq6; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq1 hcq2; omega) (by clear * - hcq9; omega) (by clear * - hAG hcq1 hcq2; omega) (by clear * - hAG hcq0 hcq6; omega) (by clear * - hAG hcq2 hcq6; omega) hbl' (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq6 hcq9 hApos; omega)) (Or.inr (by clear * - hAG hcq1 hcq2 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCDEFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq9 hcq11 hcq12 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1493 A.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1494 A.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2190 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAC hcq2 hcq0 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1495 A.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2320 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hAC hcq2 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2191 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hAC h hcq13)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1129 A.natDegree C.natDegree D.natDegree hApos h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1130 A.natDegree C.natDegree D.natDegree hAC h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1487 A.natDegree C.natDegree D.natDegree E.natDegree hAC h hcq2 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1497 A.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1528 A.natDegree C.natDegree D.natDegree G.natDegree h hAC hcq2 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1498 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq2 hcq0)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq2; omega) (by clear * - hcq1; omega) (by clear * - hAC hcq0 hcq2; omega) (by clear * - hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCDEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq3 hcq4 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1499 A.natDegree C.natDegree D.natDegree F.natDegree hcq9 h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1500 A.natDegree C.natDegree D.natDegree F.natDegree hcq9 h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2192 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq9 hcq0 hcq12 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1501 A.natDegree C.natDegree D.natDegree F.natDegree h hcq9 hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2321 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq9 hcq1 hcq0 hcq12)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2193 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq9 h hcq0 hcq12 hcq7)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1503 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1504 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2194 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq12 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1505 A.natDegree C.natDegree D.natDegree F.natDegree h hcq9 hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2322 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq9 hcq1 hcq0 hcq12)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1506 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq12)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq12; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDEFG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2195 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 hcq11 hBn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1507 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_1508 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_2196 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq3 hcq11 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1509 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2323 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq1 hcq11)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2198 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq11 hcq2)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2199 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 hcq11 hBn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1511 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_1512 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_2200 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 hcq11 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1513 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2324 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq1 hcq11)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1514 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq11)
  have hbdelta' : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2202 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 hcq11 hBn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1515 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1516 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_2203 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 hcq11 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1517 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_2325 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq1 hcq11)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1518 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq11; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

end QuarticChamberKills810

end Max11DegreeRoutes
