import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart06Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart07Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart08Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart09Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart10Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart11Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart12Scratch
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
/-- Chamber `BCDEG` / `BG·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1770 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1368 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2065 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1370 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq7 hcq3 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1371 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2382 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq1 h hcq7 hcq2 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1772 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1375 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2067 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1377 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq7 hcq3 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1378 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2383 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq1 h hcq7 hcq2 hcq3)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1380 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1774 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1382 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2069 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1384 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq7 hcq3 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1385 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1775 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq0 hcq1 hcq7 hcq3)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq2 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq6 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2384 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq6 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2071 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2072 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2073 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2385 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq6 h hcq7 hcq2 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2386 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq6 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2076 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2077 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq2 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2078 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2387 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq6 h hcq7 hcq2 hcq1)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq6 hcq7; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq1 hcq2 hcq6 hcq7; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq2 hcq7; omega) (by clear * - hcq6 hcq7; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·DD·DE·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2384 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq3 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2080 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2081 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1370 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq7 hcq4 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2082 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2388 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq3 h hcq7 hcq1 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2386 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq3 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2084 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2085 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1377 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq7 hcq4 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2086 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2389 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq3 h hcq7 hcq1 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2088 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq7 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2390 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq3 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2089 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2090 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1384 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq7 hcq4 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2091 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq1 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2391 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq3 hcq7 hcq1 hcq4)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq3 hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq7; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1770 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq3 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1387 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2093 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq7 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1388 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2392 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq3 h hcq7 hcq1 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1772 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq3 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1390 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2095 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1391 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2393 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq3 h hcq7 hcq1 hcq4)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq4 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1894 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2097 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1432 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1433 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq0 hcq7 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1434 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2394 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq5 h hcq0 hcq7 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1896 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2099 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1439 A.natDegree B.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1440 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq0 hcq7 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1441 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2395 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq5 h hcq0 hcq7 hcq3)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1443 A.natDegree B.natDegree E.natDegree G.natDegree hcq0 hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1898 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2101 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1446 A.natDegree B.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1447 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq0 hcq7 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1448 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2396 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq5 hcq0 hcq7 hcq3)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq7; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1894 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2103 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1449 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1450 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2397 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq1 h hcq0 hcq7 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1896 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2105 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1452 A.natDegree B.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1453 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2398 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq1 h hcq0 hcq7 hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq5 hcq7 hzero; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq4 hcq6 hcq7; omega) (by clear * - hcq0 hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq6 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq6 hcq7; omega) (by clear * - hcq0 hcq4 hcq6 hcq7; omega) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCDEG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hFn hcq0 hcq7 hcq8 hApos hcq15 hcq16 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1186 A.natDegree B.natDegree C.natDegree D.natDegree hAC h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1187 A.natDegree B.natDegree C.natDegree D.natDegree hAC h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1188 A.natDegree B.natDegree C.natDegree D.natDegree hAC h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1641 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hAC hcq8 hcq2 hcq16)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1778 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hAC hcq8 hcq2 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2399 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAC h hcq8 hcq2 hcq16 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1190 A.natDegree B.natDegree C.natDegree D.natDegree hAC h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq8 hcq16)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1300 A.natDegree B.natDegree C.natDegree G.natDegree h hAC hcq8 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1643 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos h hcq8 hcq2 hcq16)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq8 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1192 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq8 hcq16)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1301 A.natDegree B.natDegree C.natDegree G.natDegree h hAC hcq8 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1193 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq8 hcq2)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq8; omega) (by clear * - hAC hcq8; omega) (by clear * - hcq2; omega) (by clear * - hcq8 hcq16; omega) (by clear * - hAC hcq2 hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq2 hcq8 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG27810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq6 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1780 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 h hcq0 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1781 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 h hcq0 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1782 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 h hcq0 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2400 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq0 hcq1 hcq5 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1306 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq14 hcq0 hFn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1783 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq14 hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2401 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq0 hcq1 hcq5 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1309 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1310 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1785 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 h hcq0 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1905 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq14 h hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1313 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq14 hcq0 hFn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1314 A.natDegree B.natDegree C.natDegree G.natDegree h hcq14 hcq0 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2402 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq0 hcq1 hcq5 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1316 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1317 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1787 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 h hcq0 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1907 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq14 h hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1320 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq14 hcq0 hFn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1321 A.natDegree B.natDegree C.natDegree G.natDegree h hcq14 hcq0 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1788 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq14 hcq0 hcq1 hcq6)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq6 hcq14; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq5 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq14; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG29810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq3 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2403 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 hcq3 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2404 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 hcq3 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2405 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 hcq3 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2406 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq3 hcq1 hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2407 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq14 hcq3 hcq1 hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2408 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq14 hcq3 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2409 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 hcq3 h hcq1 hcq2 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2410 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2411 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2412 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 hcq3 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2413 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 hcq3 h hcq1 hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2414 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq14 hcq3 hcq1 hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2415 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq14 hcq3 hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2416 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 hcq3 h hcq1 hcq2 hcq0)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ D.natDegree + E.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2417 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_2418 A.natDegree B.natDegree C.natDegree G.natDegree hcq14 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2419 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq14 hcq3 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2420 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 hcq3 h hcq1 hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2421 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq14 hcq3 hcq1 hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2422 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq14 hcq3 hcq1 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2423 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq3 hcq1 hcq2 hcq0)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq2 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq2 hcq3 hcq14; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq14; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq6 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2424 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq14 h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2287 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq14 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2288 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq14 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2289 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq14 hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2425 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq14 hcq6 hcq2 hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2290 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq14 hcq2 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2426 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq14 h hcq6 hcq2 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq2 hcq6 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·DD·DG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEG34810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG34810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq3 hcq6 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq6 hcq14; omega) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
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
/-- Chamber `BCDEG` / `CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG35810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG35810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2427 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2428 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2429 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2430 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq1 hcq2 hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2431 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq1 hcq0 hcq5 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2432 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq1 hcq2 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2433 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2434 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2435 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2436 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2437 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq2 hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2438 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq1 hcq0 hcq5 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2439 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq1 hcq2 hcq0 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2440 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq1 hcq0 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2441 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 hcq1 hcq2 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2442 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2443 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2444 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq2 hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2445 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq1 hcq0 hcq5 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2446 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq2 hcq0 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2447 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq1 hcq2 hcq0 hcq5)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq2 hcq5 hcq14; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG37810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG37810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2448 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq3 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2297 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2298 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq14 h hcq4 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2299 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq4 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2449 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq3 hcq1 hcq0 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2300 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq14 hcq4 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2450 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hApos hcq14 h hcq3 hcq4 hcq1 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq0 hcq3 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq4 hcq14; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG38810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG38810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq5 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1789 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq14 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1790 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq14 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1791 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq14 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2451 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq14 hcq1 hcq2 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1325 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq1 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1792 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree h hcq0 hcq14 hcq1 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2452 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq14 h hcq1 hcq2 hcq6)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq2; omega) (by clear * - hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq6; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEG39810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG39810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1081 A.natDegree B.natDegree D.natDegree hcq9 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1194 A.natDegree B.natDegree C.natDegree D.natDegree hcq8 hcq14 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1082 A.natDegree B.natDegree D.natDegree hAB hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1328 A.natDegree B.natDegree D.natDegree E.natDegree h hcq2 hAB hAD)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1393 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hAB hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2453 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq3 hAB hcq14 h hAD hcq12)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1084 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1196 A.natDegree B.natDegree C.natDegree D.natDegree hcq8 hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_1085 A.natDegree B.natDegree D.natDegree hApos h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1330 A.natDegree B.natDegree D.natDegree E.natDegree hcq2 hAB h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1395 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hAB)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1645 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hcq2 h hcq14 hcq7 hcq12)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1087 A.natDegree B.natDegree D.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1198 A.natDegree B.natDegree C.natDegree D.natDegree hcq8 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1088 A.natDegree B.natDegree D.natDegree hApos h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1332 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq2 h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1396 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1199 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq8 hcq14)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq8; omega) (by clear * - hcq9; omega) (by clear * - hcq2 hcq9; omega) (by clear * - hcq12; omega) (by clear * - hcq14; omega) (by clear * - hcq1; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq7 hcq8 hApos hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq2 hcq7 hcq8 hApos; omega)) (Or.inr (by clear * - hcq7 hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG43810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG43810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hFn hcq0 hcq1 hcq5 hcq7 hcq9 hApos hcq14 hcq15 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2108 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq1 hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2307 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1614 A.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1615 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1616 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2454 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq1 h hAD hcq0 hcq6)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq6; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq6; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq6; omega) (by clear * - hAD hcq0 hcq1 hcq6; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEG48810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG48810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1397 A.natDegree B.natDegree D.natDegree G.natDegree hcq2 hcq0 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_0845 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1054 A.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hAD hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2455 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 h hAD hcq3 hcq6)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hAD hcq0 hcq2 hcq3; omega) (by clear * - hAD hcq0 hcq2; omega) (by clear * - hAD hcq0 hcq2 hcq6; omega) (by clear * - hAD hcq0 hcq2 hcq3; omega) (by clear * - hAD hcq0 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq6; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq2 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEG49810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG49810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hFn hcq0 hcq2 hcq5 hcq10 hcq16 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1333 A.natDegree B.natDegree D.natDegree E.natDegree hcq10 hcq7 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1646 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq14 h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1334 A.natDegree B.natDegree D.natDegree E.natDegree hcq10 hAE h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1335 A.natDegree B.natDegree D.natDegree E.natDegree h hcq10 hAE hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2111 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq10 hAE hcq2 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2456 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq10 hcq16 hAE h hcq2 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1093 A.natDegree B.natDegree E.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1204 A.natDegree B.natDegree C.natDegree E.natDegree hcq14 h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1337 A.natDegree B.natDegree D.natDegree E.natDegree hcq10 hAE h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1094 A.natDegree B.natDegree E.natDegree hApos hcq10 h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1457 A.natDegree B.natDegree E.natDegree G.natDegree h hcq10 hAE hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1648 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos hcq10 hcq16 h hcq14 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1096 A.natDegree B.natDegree E.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1206 A.natDegree B.natDegree C.natDegree E.natDegree h hcq14 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1339 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq10 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1097 A.natDegree B.natDegree E.natDegree hApos hcq10 h)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1458 A.natDegree B.natDegree E.natDegree G.natDegree h hcq10 hAE hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1649 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hApos h hcq14 hcq8 hcq2)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq8; omega) (by clear * - hcq10; omega) (by clear * - hcq2; omega) (by clear * - hcq10; omega) (by clear * - hcq2 hcq10 hcq16; omega) (by clear * - hcq14; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq7 hcq8 hApos hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq7 hApos hcq10; omega)) (Or.inr (by clear * - hcq2 hcq7 hApos hcq10; omega)) (Or.inr (by clear * - hcq8 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberBCDEG52810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG52810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq6 hcq8 hApos hcq14 hcq15 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1650 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1651 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1652 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1653 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq16 hcq0 hcq9 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1654 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq16 hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2457 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq16 hcq0 hcq9 hcq3 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2458 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq16 hcq0 h hcq9 hcq3 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1657 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1658 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1659 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1660 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1661 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq16 hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2459 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq16 hcq0 hcq9 hcq3 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1663 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq9)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1664 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq0 hcq9 hcq3 h)
      · exact Or.inr (astra4u_Round4Package_nat_1665 A.natDegree C.natDegree D.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1666 A.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1667 A.natDegree C.natDegree D.natDegree E.natDegree hcq16 hcq0 h hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1668 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq16 hcq0 hcq9 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2460 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq16 hcq0 hcq3 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1670 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree h hcq16 hcq0 hcq9)
  have hrest : (xiQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest2810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq9 hcq16; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq3 hcq9; omega) (by clear * - hcq0 hcq3 hcq9 hcq16; omega) (by clear * - hcq0 hcq9 hcq16; omega) (by clear * - hcq0 hcq2 hcq9 hcq16; omega) (by clear * - hcq0 hcq3 hcq9 hcq16; omega) (by clear * - hcq0 hcq3 hcq16; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq9 hcq16; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq9 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq9 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq9 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq9 hcq16; omega))
  have hlead : (xiQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace2810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEG53810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG53810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hFn hcq0 hcq2 hcq4 hApos hcq10 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2113 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq2 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2461 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq2 hcq4 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2114 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq2 hcq4 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2115 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq2 hcq4 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2116 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq2 hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2462 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq2 hcq4 hcq0 hcq3)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hAE hcq0 hcq2 hcq3; omega) (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq4; omega) (by clear * - hAE hcq0 hcq2; omega) (by clear * - hAE hcq0 hcq2 hcq3 hcq4; omega) (by clear * - hAE hcq0 hcq3; omega) (by clear * - hcq3; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEG54810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG54810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAC hAD hAE hFn hcq0 hcq2 hcq5 hcq7 hApos hcq14 hzero; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hAG hcq0; omega) (by clear * - hAG hcq0 hcq2; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq0; omega) (by clear * - hAG hcq0 hcq2 hcq5; omega) (by clear * - hAG hcq1 hcq2; omega) (by clear * - hAG hcq0 hcq1 hcq5; omega) (by clear * - hAG hcq0 hcq2; omega) (by clear * - hAG hcq0 hcq1 hcq2; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq0 hcq2; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq5; omega) (by clear * - hAG hcq2 hcq5; omega) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq9 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1101 A.natDegree B.natDegree E.natDegree F.natDegree hcq9 hEn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1463 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2463 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hcq0 h hcq9 hcq4 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq9 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1108 A.natDegree B.natDegree E.natDegree F.natDegree hcq9 hEn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1465 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1672 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq9 hcq4 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq9 h)
      · exact Or.inr (astra4u_Round4Package_nat_1212 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq9 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1115 A.natDegree B.natDegree E.natDegree F.natDegree hcq9 hEn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1466 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1673 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq9 hcq4 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq1 hcq9; omega) (by clear * - hcq6 hcq9; omega) (by clear * - hcq3; omega) (by clear * - hcq1 hcq4 hcq9; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq9 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq9 hApos; omega)) (Or.inr (by clear * - hcq4 hcq6 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq9; omega)) (Or.inr (by clear * - hcq9 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BF·BG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1913 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq9 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1101 A.natDegree B.natDegree E.natDegree F.natDegree hcq9 hEn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1467 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2464 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2 hcq4 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1915 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq9 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1108 A.natDegree B.natDegree E.natDegree F.natDegree hcq9 hEn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1469 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2465 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2 hcq4 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq9 h)
      · exact Or.inr (astra4u_Round4Package_nat_1917 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq9 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1115 A.natDegree B.natDegree E.natDegree F.natDegree hcq9 hEn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1470 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2466 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2 hcq4 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq6 hcq9; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq2 hcq4 hcq9; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq2; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq9; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

end QuarticChamberKills810

end Max11DegreeRoutes
