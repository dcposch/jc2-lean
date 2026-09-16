import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart06Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart07Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart08Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart10Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart11Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
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
/-- Chamber `CDEF` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCDEF2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq2 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1499 A.natDegree C.natDegree D.natDegree F.natDegree hcq6 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1500 A.natDegree C.natDegree D.natDegree F.natDegree hcq6 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2192 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq7 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1501 A.natDegree C.natDegree D.natDegree F.natDegree h hcq6 hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2193 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq7 hcq5)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1503 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1504 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2194 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq7 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1505 A.natDegree C.natDegree D.natDegree F.natDegree h hcq6 hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1506 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq7)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDEF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2195 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq2 hcq6 hBn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1507 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_1508 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_2196 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq2 hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1509 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_2197 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq2 hcq6 hcq1 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2198 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq2 h hcq6 hcq1)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2199 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq2 hcq6 hBn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1511 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_1512 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_2200 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq2 hcq6 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1513 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_2201 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq2 hcq6 hcq1 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1514 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq6)
  have hbdelta' : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2202 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq2 hcq6 hBn hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1515 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1516 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_2203 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq2 hcq6 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1517 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_2204 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq2 hcq6 hcq1 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1518 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 h)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDEF5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2205 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2206 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2207 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq2 hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2208 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2209 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq2 hcq7 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2210 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2211 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2212 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq2 hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2213 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2214 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq2 hcq7 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq2 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq2 hcq7; omega) (by clear * - hcq1 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·DD·DE·EE` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberCDEF6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2215 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq6 hBn hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2216 A.natDegree C.natDegree D.natDegree F.natDegree hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_2217 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq6 h hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2218 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2219 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq6 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_2220 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq1 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2221 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq6 hcq1 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2222 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq6 hBn hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2223 A.natDegree C.natDegree D.natDegree F.natDegree hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_2224 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq6 h hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2225 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2226 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq6 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_2227 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq1 hcq4 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2228 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq6 hcq1 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2229 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq6 hBn hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2230 A.natDegree C.natDegree D.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2231 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq6 h hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2232 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2233 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq6 h hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_2234 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq1 hcq4 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2235 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq6 hcq1 hcq4)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq4 hcq6; omega) (by clear * - hcq1 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEF9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq3 hcq4 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1538 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq6 hcq0 hBn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2236 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2237 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2238 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2239 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq2 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1543 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq0 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2240 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq4)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_1545 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq6 hcq0 hBn hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_2241 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq2 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_2242 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq2 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_2243 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq2 hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_2244 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq2 hcq4)
    · exact absurd h (astra4u_Round4Package_nat_1550 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 hcq0 hcq4 hGn)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq2 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEF11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1551 A.natDegree C.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2245 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1552 A.natDegree C.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1553 A.natDegree C.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2246 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq1 hcq4)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1555 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2247 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1556 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1557 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2248 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq0 hcq1 h hcq4)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq1 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDEF12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq4 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1147 A.natDegree C.natDegree F.natDegree hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_1519 A.natDegree C.natDegree D.natDegree F.natDegree hcq3 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_1558 A.natDegree C.natDegree E.natDegree F.natDegree h hcq6 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1148 A.natDegree C.natDegree F.natDegree h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2249 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq0 h hcq6 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1150 A.natDegree C.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1521 A.natDegree C.natDegree D.natDegree F.natDegree hcq3 hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_1560 A.natDegree C.natDegree E.natDegree F.natDegree hcq6 h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2250 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq3 hcq0 hcq5)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq5 hcq6; omega) (by clear * - hcq0 hcq3 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDEF13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1132 A.natDegree C.natDegree D.natDegree hcq6 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1156 A.natDegree D.natDegree E.natDegree h hcq1 hAD)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2251 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hAD hcq2)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1134 A.natDegree C.natDegree D.natDegree hApos hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1158 A.natDegree D.natDegree E.natDegree hcq1 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1167 A.natDegree D.natDegree F.natDegree h hAD hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1524 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq6 hcq2)
  have hbdelta' : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1136 A.natDegree C.natDegree D.natDegree hApos h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1069 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1159 A.natDegree D.natDegree E.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_1169 A.natDegree D.natDegree F.natDegree hAD h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1070 A.natDegree G.natDegree hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1170 A.natDegree D.natDegree F.natDegree h hcq2)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq6; omega) (by clear * - hcq2; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq6; omega)) (Or.inr (by clear * - hcq6 hApos; omega)) (Or.inr (by clear * - hcq6; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDEF15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2252 A.natDegree C.natDegree D.natDegree F.natDegree hcq5 hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1591 A.natDegree D.natDegree F.natDegree hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1592 A.natDegree D.natDegree E.natDegree F.natDegree h hAD hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1593 A.natDegree D.natDegree F.natDegree h hAD hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2253 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq5 h hAD hcq0 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2254 A.natDegree C.natDegree D.natDegree F.natDegree hcq5 hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1595 A.natDegree D.natDegree F.natDegree hApos h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1596 A.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2255 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq5 h hAD hcq0 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEF19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hGn hcq0 hcq1 hcq4 hcq6 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2256 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2257 A.natDegree D.natDegree E.natDegree F.natDegree hcq4 hAE h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2258 A.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hAE hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2259 A.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hAE hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2260 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 h hAE)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_2261 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq8 hcq4 h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_2262 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq4 hAE h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_2263 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq8 hcq4 h hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_2264 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq4 hAE hcq3)
    · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq1; omega) (by clear * - hcq6; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq4; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCDEF20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq5 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2265 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq8 hcq0 hcq2 hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2266 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2267 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2268 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq0 hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2269 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq0 hcq1 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_2270 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq8 hcq0 hcq2 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2271 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2272 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq8 hcq0 hcq2 hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2273 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2274 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2275 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h hcq1 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2276 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq0 hcq1 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_2277 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq8 hcq0 hcq2 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2278 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2279 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq8 hcq0 hcq2 hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1665 A.natDegree C.natDegree D.natDegree E.natDegree h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1666 A.natDegree C.natDegree D.natDegree E.natDegree hcq8 hcq0 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1667 A.natDegree C.natDegree D.natDegree E.natDegree hcq8 hcq0 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2280 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq0 h hcq1 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_2281 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq8 hcq0 hcq2 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2282 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq0 hcq1)
  have hrest : (xiQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq0 hcq1 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega))
  have hlead : (xiQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace2810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEF21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hGn hcq0 hcq2 hcq3 hcq6 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1568 A.natDegree C.natDegree E.natDegree F.natDegree hAE h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1608 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2283 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAE hcq2 hcq0 hcq5)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1570 A.natDegree C.natDegree E.natDegree F.natDegree hAE h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1610 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1571 A.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1572 A.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2284 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq2 hcq0 h hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq5; omega) (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

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
/-- Chamber `CDEF` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDEF22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAD hAE hBn hGn hcq0 hcq1 hcq4 hcq6 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1152 A.natDegree C.natDegree F.natDegree hcq0 hAF h)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1175 A.natDegree E.natDegree F.natDegree h hAF hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2285 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hAF hcq4 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1154 A.natDegree C.natDegree F.natDegree hcq0 h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1173 A.natDegree D.natDegree F.natDegree hAF h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1177 A.natDegree E.natDegree F.natDegree hAF h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2286 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq4 hcq1)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq1; omega) (by clear * - hAF hcq0 hcq4; omega) (by clear * - hAF hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCDEG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hFn hcq0 hcq1 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1126 A.natDegree C.natDegree D.natDegree hAC h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1127 A.natDegree C.natDegree D.natDegree hAC h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1485 A.natDegree C.natDegree D.natDegree E.natDegree h hAC hcq1 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1527 A.natDegree C.natDegree D.natDegree G.natDegree h hAC hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1486 A.natDegree C.natDegree D.natDegree E.natDegree hAC h hcq8)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1129 A.natDegree C.natDegree D.natDegree hApos h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1130 A.natDegree C.natDegree D.natDegree hAC h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1487 A.natDegree C.natDegree D.natDegree E.natDegree hAC h hcq1 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1528 A.natDegree C.natDegree D.natDegree G.natDegree h hAC hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1131 A.natDegree C.natDegree D.natDegree hApos h hcq1)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq1; omega) (by clear * - hcq0; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `CG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hFn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2287 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2288 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2289 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq6 hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2290 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq6 hcq2 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2291 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 h hcq2 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2292 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2293 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2294 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 h hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2295 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq6 hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2296 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq6 h hcq2 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq2 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `CG·DD·DG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hFn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq0 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq5 hcq6; omega) (by clear * - hcq0 hcq5 hcq6; omega) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hFn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2297 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq6 h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2298 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq6 h hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2299 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq6 hcq3 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2300 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq6 hcq3 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2301 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq6 h hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2302 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq6 h hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2303 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq6 h hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2304 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq6 h hcq3 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2305 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq6 hcq3 hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2306 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq3 hcq1 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq3 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDEG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1132 A.natDegree C.natDegree D.natDegree hcq6 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1156 A.natDegree D.natDegree E.natDegree h hcq1 hAD)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1529 A.natDegree D.natDegree G.natDegree h hcq2 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1488 A.natDegree C.natDegree D.natDegree E.natDegree hcq1 h hcq6 hAD)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1134 A.natDegree C.natDegree D.natDegree hApos hcq6 h)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1158 A.natDegree D.natDegree E.natDegree hcq1 hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1530 A.natDegree D.natDegree G.natDegree h hcq2 hAD)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1135 A.natDegree C.natDegree D.natDegree hApos h hcq6)
  have hbdelta' : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_1136 A.natDegree C.natDegree D.natDegree hApos h hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_1069 A.natDegree D.natDegree hApos h)
    · exact Or.inr (astra4u_Round4Package_nat_1159 A.natDegree D.natDegree E.natDegree hApos hcq1 h)
    · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
    · exact Or.inr (astra4u_Round4Package_nat_1531 A.natDegree D.natDegree G.natDegree hApos h hcq2)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq6; omega) (by clear * - hcq0; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq6; omega)) (Or.inr (by clear * - hcq6 hApos; omega)) (Or.inr (by clear * - hcq6; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hFn hcq0 hcq1 hcq5 hcq6 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2307 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1614 A.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1615 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1616 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2308 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hAD hcq0 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2309 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1618 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1619 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1620 A.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2310 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h hcq0 hcq5)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDEG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0845 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1054 A.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hAD hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2311 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hAD hcq2 hcq5)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0851 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1056 A.natDegree D.natDegree E.natDegree G.natDegree hcq0 hAD h hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0854 A.natDegree D.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1533 A.natDegree C.natDegree D.natDegree G.natDegree hApos h hcq0 hcq2)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hAD hcq0 hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hFn hcq0 hcq1 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1489 A.natDegree C.natDegree D.natDegree E.natDegree hcq8 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1160 A.natDegree D.natDegree E.natDegree hAE h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1161 A.natDegree D.natDegree E.natDegree h hAE hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2312 A.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1490 A.natDegree C.natDegree D.natDegree E.natDegree hcq8 h hAE)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1491 A.natDegree C.natDegree D.natDegree E.natDegree hcq8 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1163 A.natDegree D.natDegree E.natDegree hAE h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1164 A.natDegree D.natDegree E.natDegree hApos h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2313 A.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1492 A.natDegree C.natDegree D.natDegree E.natDegree hApos h hcq6 hcq1)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq1; omega) (by clear * - hcq6; omega) (by clear * - hcq0; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hFn hcq0 hcq2 hcq3 hcq6 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2314 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq3 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1160 A.natDegree D.natDegree E.natDegree hAE h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1161 A.natDegree D.natDegree E.natDegree h hAE hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2315 A.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq3 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2316 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq0 hcq2)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2317 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq3 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1163 A.natDegree D.natDegree E.natDegree hAE h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1164 A.natDegree D.natDegree E.natDegree hApos h hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2318 A.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq3 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2319 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq3 hcq0 hcq2)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq3; omega) (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAD hAE hBn hFn hcq0 hcq1 hcq4 hcq6 hApos hzero; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq0; omega) (by clear * - hAG hcq0; omega) (by clear * - hAG hcq0 hcq4; omega) (by clear * - hAG hcq1 hcq4; omega) (Or.inr (by clear * - hAG hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCDFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hcq0 hcq5 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1493 A.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1494 A.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1495 A.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2320 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hAC hcq2 hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1496 A.natDegree C.natDegree D.natDegree F.natDegree hAC h)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1129 A.natDegree C.natDegree D.natDegree hApos h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1130 A.natDegree C.natDegree D.natDegree hAC h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1497 A.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1528 A.natDegree C.natDegree D.natDegree G.natDegree h hAC hcq2 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1498 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq2 hcq0)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq2; omega) (by clear * - hcq1; omega) (by clear * - hAC hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

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
/-- Chamber `CDFG` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCDFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1499 A.natDegree C.natDegree D.natDegree F.natDegree hcq5 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1500 A.natDegree C.natDegree D.natDegree F.natDegree hcq5 h hcq0 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1501 A.natDegree C.natDegree D.natDegree F.natDegree h hcq5 hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2321 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq5 hcq1 hcq0 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1502 A.natDegree C.natDegree D.natDegree F.natDegree hcq5 h hcq0 hcq8)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1503 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1504 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1505 A.natDegree C.natDegree D.natDegree F.natDegree h hcq5 hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2322 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq5 hcq1 hcq0 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1506 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq8)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CF·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1507 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1508 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1509 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2323 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq2 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1510 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 h hcq7)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1511 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1512 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1513 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2324 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq2 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1514 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq7)
  have hbdelta' : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1515 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1516 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1517 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_2325 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq2 hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1518 A.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq2 h)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hApos; omega)) (Or.inr (by clear * - hcq0 hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hcq0 hcq1 hcq2 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1147 A.natDegree C.natDegree F.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1519 A.natDegree C.natDegree D.natDegree F.natDegree hcq3 hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1148 A.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1578 A.natDegree C.natDegree F.natDegree G.natDegree h hcq7 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2326 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq0 h hcq7 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1150 A.natDegree C.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1521 A.natDegree C.natDegree D.natDegree F.natDegree hcq3 hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1579 A.natDegree C.natDegree F.natDegree G.natDegree h hcq7 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1522 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq3 hcq0)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq3 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CG·DD·DG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG17810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hcq0 hcq1 hcq3 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2327 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2328 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2329 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hcq1 hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2330 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hcq1 hcq0 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2331 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos hcq7 h hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2332 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2333 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2334 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hcq1 hcq0 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2335 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq7 hcq1 hcq0 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2336 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos hcq7 h hcq1 hcq0 hcq4)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq7; omega) (by clear * - hcq4 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1132 A.natDegree C.natDegree D.natDegree hcq7 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1529 A.natDegree D.natDegree G.natDegree h hcq3 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1523 A.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hAD hcq2)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1134 A.natDegree C.natDegree D.natDegree hApos hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1167 A.natDegree D.natDegree F.natDegree h hAD hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1530 A.natDegree D.natDegree G.natDegree h hcq3 hAD)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1524 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq7 hcq2)
  have hbdelta' : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1136 A.natDegree C.natDegree D.natDegree hApos h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1069 A.natDegree D.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1169 A.natDegree D.natDegree F.natDegree hAD h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1531 A.natDegree D.natDegree G.natDegree hApos h hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1170 A.natDegree D.natDegree F.natDegree h hcq2)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq7; omega) (by clear * - hcq1; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq2; omega)) (Or.inr (by clear * - hcq7; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0845 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2337 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hAD hcq3 hcq4)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0851 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1167 A.natDegree D.natDegree F.natDegree h hAD hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0854 A.natDegree D.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2338 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq0 hcq3 hcq4)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hAD hcq0 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDFG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAD hBn hEn hcq0 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1152 A.natDegree C.natDegree F.natDegree hcq0 hAF h)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq5 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2339 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 hcq0 h hAF hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1154 A.natDegree C.natDegree F.natDegree hcq0 h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1173 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1580 A.natDegree F.natDegree G.natDegree h hcq5 hAF)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1526 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq2)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq2; omega) (by clear * - hAF hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAD hBn hEn hcq0 hcq2 hcq4 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1581 A.natDegree C.natDegree F.natDegree G.natDegree hAF h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2340 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hAF hcq0 hcq3 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1583 A.natDegree C.natDegree F.natDegree G.natDegree h hAF hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1173 A.natDegree D.natDegree F.natDegree hAF h hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1584 A.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2341 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq0 hcq3 hcq4)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq4; omega) (by clear * - hAF hcq0 hcq3 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAD hAF hBn hEn hcq1 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1586 A.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1627 A.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq2 hAG h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2342 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos hcq1 hcq2 h hAG)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1588 A.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1629 A.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq2 hAG h)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1182 A.natDegree F.natDegree G.natDegree h hAG hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1183 A.natDegree F.natDegree G.natDegree hApos h hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2343 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos hcq1 hcq2 h hAG hcq5)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hAG hcq1 hcq2; omega) (by clear * - hAG hcq1; omega) (by clear * - hcq5; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq2 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hAG hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCEFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq5 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1137 A.natDegree C.natDegree F.natDegree hAC h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1534 A.natDegree C.natDegree E.natDegree F.natDegree h hAC hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1138 A.natDegree C.natDegree F.natDegree h hAC hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1574 A.natDegree C.natDegree F.natDegree G.natDegree h hAC hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1139 A.natDegree C.natDegree F.natDegree h hAC)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 3 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_1140 A.natDegree C.natDegree F.natDegree hApos h hcq0)
    · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
    · exact Or.inr (astra4u_Round4Package_nat_1535 A.natDegree C.natDegree E.natDegree F.natDegree hAC h hcq0 hcq8)
    · exact Or.inr (astra4u_Round4Package_nat_1141 A.natDegree C.natDegree F.natDegree h hAC hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_1575 A.natDegree C.natDegree F.natDegree G.natDegree h hAC hcq0 hcq1)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq1; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq2 hcq5 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1142 A.natDegree C.natDegree F.natDegree hcq5 h)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1536 A.natDegree C.natDegree E.natDegree F.natDegree h hcq5 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1143 A.natDegree C.natDegree F.natDegree h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1576 A.natDegree C.natDegree F.natDegree G.natDegree h hcq5 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1144 A.natDegree C.natDegree F.natDegree h hcq5 hcq0)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 3 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_1145 A.natDegree C.natDegree F.natDegree hApos h hcq0)
    · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
    · exact Or.inr (astra4u_Round4Package_nat_1537 A.natDegree C.natDegree E.natDegree F.natDegree hcq5 h hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_1146 A.natDegree C.natDegree F.natDegree h hcq5)
    · exact Or.inr (astra4u_Round4Package_nat_1577 A.natDegree C.natDegree F.natDegree G.natDegree h hcq5 hcq1)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hdpos; omega)) (Or.inr (by clear * - hcq0 hApos hdpos; omega)) (Or.inr (by clear * - hcq0 hcq2 hdpos; omega)) (Or.inr (by clear * - hdpos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq2 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1538 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 hcq0 hBn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1539 A.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1540 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq0 hDn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1541 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1542 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2344 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq7 hcq0 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1544 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq2)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_1545 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 hcq0 hBn hcq2)
    · exact Or.inr (astra4u_Round4Package_nat_1546 A.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq2)
    · exact absurd h (astra4u_Round4Package_nat_1547 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq0 hDn hcq2)
    · exact Or.inr (astra4u_Round4Package_nat_1548 A.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq2)
    · exact Or.inr (astra4u_Round4Package_nat_1549 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq2)
    · exact Or.inr (astra4u_Round4Package_nat_2345 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq7 hcq0 hcq2)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq7 hdpos; omega)) (Or.inr (by clear * - hcq0 hcq2 hdpos; omega)) (Or.inr (by clear * - hdpos; omega)) (Or.inr (by clear * - hcq0 hcq7 hdpos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

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
/-- Chamber `CEFG` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq3 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1551 A.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1552 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1553 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2346 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0 hcq1 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1554 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq1)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_1555 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0)
    · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
    · exact Or.inr (astra4u_Round4Package_nat_1556 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_1557 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
    · exact Or.inr (astra4u_Round4Package_nat_2347 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq0 hcq1 hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq0 hcq7; omega) (by clear * - hcq1 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCEFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq2 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1147 A.natDegree C.natDegree F.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1558 A.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1148 A.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1578 A.natDegree C.natDegree F.natDegree G.natDegree h hcq7 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1559 A.natDegree C.natDegree E.natDegree F.natDegree hcq0 h hcq7 hcq3)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1150 A.natDegree C.natDegree F.natDegree hApos hcq0 h)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1560 A.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1579 A.natDegree C.natDegree F.natDegree G.natDegree h hcq7 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1151 A.natDegree C.natDegree F.natDegree hApos h hcq0)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq3 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCEFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG17810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq3 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2348 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq3 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2349 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2350 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2351 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2352 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2353 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq3 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2354 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2355 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2356 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq7 hcq3 hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2357 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq3 hcq1)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq2 hcq3 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1561 A.natDegree C.natDegree E.natDegree F.natDegree hcq8 hcq2 h)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1562 A.natDegree E.natDegree F.natDegree h hcq2 hAE)
      · exact Or.inr (astra4u_Round4Package_nat_1563 A.natDegree E.natDegree F.natDegree h hcq2 hAE)
      · exact Or.inr (astra4u_Round4Package_nat_2358 A.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hAE hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1564 A.natDegree C.natDegree E.natDegree F.natDegree h hcq8 hAE)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_1565 A.natDegree C.natDegree E.natDegree F.natDegree hcq8 hcq2 h)
    · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
    · exact Or.inr (astra4u_Round4Package_nat_1566 A.natDegree E.natDegree F.natDegree hApos hcq2 h)
    · exact Or.inr (astra4u_Round4Package_nat_1567 A.natDegree E.natDegree F.natDegree h hcq2 hAE)
    · exact Or.inr (astra4u_Round4Package_nat_2359 A.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hAE hcq3)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq7; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq7; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq7; omega)) (Or.inr (by clear * - hcq7; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `EE·EF·EG·FF·FG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEFG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq5 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2360 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq0 hcq1 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2180 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2361 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq1 hcq6)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_2362 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq0 hcq1 hcq6)
    · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
    · exact Or.inr (astra4u_Round4Package_nat_1571 A.natDegree E.natDegree F.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_1572 A.natDegree E.natDegree F.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_2363 A.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq0 hcq1)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hAE hcq1 hcq6; omega) (by clear * - hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq2 hcq3 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1568 A.natDegree C.natDegree E.natDegree F.natDegree hAE h hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2182 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1569 A.natDegree C.natDegree E.natDegree F.natDegree h hAE hcq2 hcq0)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_1570 A.natDegree C.natDegree E.natDegree F.natDegree hAE h hcq2 hcq0)
    · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
    · exact Or.inr (astra4u_Round4Package_nat_1571 A.natDegree E.natDegree F.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_1572 A.natDegree E.natDegree F.natDegree hApos h hcq0)
    · exact Or.inr (astra4u_Round4Package_nat_2364 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq4)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq2 hcq3 hcq4 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2365 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 hAE h hcq0 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1562 A.natDegree E.natDegree F.natDegree h hcq4 hAE)
      · exact Or.inr (astra4u_Round4Package_nat_1563 A.natDegree E.natDegree F.natDegree h hcq4 hAE)
      · exact Or.inr (astra4u_Round4Package_nat_2366 A.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hAE hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2361 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq3)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_2367 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq4 hAE h hcq0 hcq3)
    · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
    · exact Or.inr (astra4u_Round4Package_nat_1566 A.natDegree E.natDegree F.natDegree hApos hcq4 h)
    · exact Or.inr (astra4u_Round4Package_nat_1567 A.natDegree E.natDegree F.natDegree h hcq4 hAE)
    · exact Or.inr (astra4u_Round4Package_nat_2368 A.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq4 hcq0)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hAE hcq0 hcq3; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCEFG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAE hBn hDn hcq0 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1152 A.natDegree C.natDegree F.natDegree hcq0 hAF h)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1175 A.natDegree E.natDegree F.natDegree h hAF hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq5 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1573 A.natDegree C.natDegree E.natDegree F.natDegree hcq0 h hAF hcq2)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1154 A.natDegree C.natDegree F.natDegree hcq0 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1177 A.natDegree E.natDegree F.natDegree hAF h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1580 A.natDegree F.natDegree G.natDegree h hcq5 hAF)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1155 A.natDegree C.natDegree F.natDegree hApos h hcq0)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hAF hcq0 hcq2; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCEFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAE hBn hDn hcq0 hcq2 hcq4 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1581 A.natDegree C.natDegree F.natDegree G.natDegree hAF h hcq0 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1631 A.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2369 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq3 hcq6)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1583 A.natDegree C.natDegree F.natDegree G.natDegree h hAF hcq0 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1633 A.natDegree E.natDegree F.natDegree G.natDegree hAF h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1584 A.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1585 A.natDegree C.natDegree F.natDegree G.natDegree hApos h hcq0 hcq3)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hAF hcq0 hcq3 hcq6; omega) (by clear * - hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCEFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAE hAF hBn hDn hcq1 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1586 A.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1636 A.natDegree E.natDegree F.natDegree G.natDegree h hAG hcq5 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2370 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAG hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1588 A.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1638 A.natDegree E.natDegree F.natDegree G.natDegree hAG h hcq5 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1182 A.natDegree F.natDegree G.natDegree h hAG hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1183 A.natDegree F.natDegree G.natDegree hApos h hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2371 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq5 hcq2)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hAG hcq1; omega) (by clear * - hcq5; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hAG hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberDEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1591 A.natDegree D.natDegree F.natDegree hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1592 A.natDegree D.natDegree E.natDegree F.natDegree h hAD hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1593 A.natDegree D.natDegree F.natDegree h hAD hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2372 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2373 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1595 A.natDegree D.natDegree F.natDegree hApos h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1596 A.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_2374 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1597 A.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1598 A.natDegree D.natDegree F.natDegree hApos h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1599 A.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1600 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_2375 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1601 A.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hAD hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberDEFG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hCn hcq0 hcq1 hcq5 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1614 A.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1615 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2376 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1616 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2377 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAD hcq0 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1618 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1619 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_2378 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1620 A.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2379 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1622 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1623 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_2380 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hAD h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1624 A.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2381 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq5)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq0 hcq1 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi

end QuarticChamberKills810

end Max11DegreeRoutes
