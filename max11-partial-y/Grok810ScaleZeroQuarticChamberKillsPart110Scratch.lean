import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart101Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart102Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart103Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart104Scratch
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
/-- Chamber `BCDFG` / `CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDFG56810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG56810 A B C D E F G)
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
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq3 hcq4 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2573 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq14 h hcq2 hcq4 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2574 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq14 h hcq2 hcq4 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2575 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq14 h hcq2 hcq4 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1324 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq0 hcq14 hcq2 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2576 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq4 hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2577 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq2 hcq4 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2578 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq14 h hcq2 hcq4)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq2 hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq1; omega) (by clear * - hcq4; omega) (by clear * - hcq0 hcq2 hcq4 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq3 hcq4; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDFG57810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG57810 A B C D E F G)
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1357 A.natDegree B.natDegree D.natDegree hcq11 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1757 A.natDegree B.natDegree C.natDegree D.natDegree hcq10 hcq14 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1358 A.natDegree B.natDegree D.natDegree hAB hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1359 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hAD hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2143 A.natDegree B.natDegree D.natDegree G.natDegree h hcq5 hAB hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2579 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq5 h hAB hcq14 hcq11 hAD hcq13 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1084 A.natDegree B.natDegree D.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1196 A.natDegree B.natDegree C.natDegree D.natDegree hcq10 hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_1085 A.natDegree B.natDegree D.natDegree hApos h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1361 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1395 A.natDegree B.natDegree D.natDegree G.natDegree h hcq5 hAB)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1759 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq14 hcq9 hcq13 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1087 A.natDegree B.natDegree D.natDegree hcq9 h)
      · exact Or.inr (astra4u_Round4Package_nat_1198 A.natDegree B.natDegree C.natDegree D.natDegree hcq10 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1088 A.natDegree B.natDegree D.natDegree hApos h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1363 A.natDegree B.natDegree D.natDegree F.natDegree hAB h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1396 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1760 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq10 hcq14 hcq0)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq10; omega) (by clear * - hcq11; omega) (by clear * - hcq0; omega) (by clear * - hcq13; omega) (by clear * - hcq14; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq3 hcq9 hApos hcq10 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos hcq10; omega)) (Or.inr (by clear * - hcq9 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDFG63810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG63810 A B C D E F G)
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
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1397 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 hcq0 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_0845 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2580 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq0 h hAD hcq5 hcq6)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hAD hcq0 hcq3 hcq5; omega) (by clear * - hAD hcq0 hcq3; omega) (by clear * - hcq0 hcq3 hcq6; omega) (by clear * - hAD hcq0 hcq3 hcq5; omega) (by clear * - hAD hcq0 hcq5; omega) (by clear * - hcq5; omega) (by clear * - hcq6; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDFG64810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG64810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAC hAD hEn hcq0 hcq4 hcq7 hcq9 hApos hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq0 h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1152 A.natDegree C.natDegree F.natDegree hcq2 hAF h)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq7 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2581 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq7 hcq2 h hAF hcq4)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hAF hcq0; omega) (by clear * - hAF hcq0 hcq2 hcq4; omega) (by clear * - hAF hcq0 hcq4; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hcq4; omega) (by clear * - hAF hcq0 hcq7; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hAF hcq2 hcq4; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDFG65810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG65810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAC hAD hEn hcq0 hcq2 hcq6 hcq9 hApos hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq2 h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1581 A.natDegree C.natDegree F.natDegree G.natDegree hAF h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2582 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hAF hcq0 hcq5 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hAF hcq2; omega) (by clear * - hAF hcq0 hcq2 hcq5 hcq6; omega) (by clear * - hAF hcq2 hcq6; omega) (by clear * - hAF hcq0 hcq2 hcq5; omega) (by clear * - hcq6; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hAF hcq0 hcq2 hcq5; omega) (by clear * - hAF hcq0 hcq5 hcq6; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDFG66810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG66810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAC hAD hAF hEn hcq1 hcq4 hcq7 hcq9 hApos hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1483 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 hAG hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_1586 A.natDegree C.natDegree F.natDegree G.natDegree hcq3 hAG h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1627 A.natDegree D.natDegree F.natDegree G.natDegree hcq5 hcq4 hAG h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2583 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos hcq3 hcq4 h hAG hcq1)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq4; omega) (by clear * - hAG hcq1 hcq3; omega) (by clear * - hAG hcq1 hcq3; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq0 hcq3; omega) (by clear * - hAG hcq3 hcq4; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq1 hcq4; omega) (by clear * - hAG hcq1 hcq3 hcq4; omega) (by clear * - hAG hcq3; omega) (by clear * - hcq7; omega) (by clear * - hAG hcq1 hcq4; omega) (by clear * - hAG hcq3; omega) (by clear * - hAG hcq3 hcq4 hcq7; omega) hbl' (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hAG hcq1 hcq3 hcq4 hcq5 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1100 A.natDegree B.natDegree D.natDegree F.natDegree hcq9 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1399 A.natDegree B.natDegree E.natDegree F.natDegree h hcq3 hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1463 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2584 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq3 hcq0 h hcq9 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1107 A.natDegree B.natDegree D.natDegree F.natDegree hcq9 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1401 A.natDegree B.natDegree E.natDegree F.natDegree hcq3 h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1465 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1797 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 hcq3 h hcq9 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq9 h)
      · exact Or.inr (astra4u_Round4Package_nat_1212 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1114 A.natDegree B.natDegree D.natDegree F.natDegree hcq9 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1403 A.natDegree B.natDegree E.natDegree F.natDegree hcq3 h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1466 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1213 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq9 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq9; omega) (by clear * - hcq6 hcq9; omega) (by clear * - hcq3 hcq6 hcq9; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq3 hcq9 hApos; omega)) (Or.inr (by clear * - hcq6 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq9; omega)) (Or.inr (by clear * - hcq9 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·BG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1913 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1100 A.natDegree B.natDegree D.natDegree F.natDegree hcq9 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2150 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1467 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2585 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2 hcq5 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1915 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1107 A.natDegree B.natDegree D.natDegree F.natDegree hcq9 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2152 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1469 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2586 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2 hcq5 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq9 h)
      · exact Or.inr (astra4u_Round4Package_nat_1917 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1114 A.natDegree B.natDegree D.natDegree F.natDegree hcq9 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2154 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1470 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1918 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq6 hcq9; omega) (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq2; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq6 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq9; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·BG·CF·CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2587 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2588 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2589 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq0 hcq3 hcq10 hDn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2590 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2591 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2592 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2593 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2594 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2595 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2596 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq0 hcq3 hcq10 hDn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2597 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2598 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2599 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2600 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq10 hcq5)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq3 hcq5 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega) (by clear * - hcq0 hcq3 hcq5 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq3 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·BG·CF·CG·FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCEFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq6 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1803 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1804 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2601 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq10 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1930 A.natDegree B.natDegree C.natDegree F.natDegree h hcq3 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1931 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2602 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq0 hcq10 hcq8)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1808 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1809 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2603 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq10 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1933 A.natDegree B.natDegree C.natDegree F.natDegree h hcq3 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1934 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2604 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq0 hcq10 hcq8)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq8 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq8 hcq10; omega) (by clear * - hcq3 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq8 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·BG·FF·FG·GG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1913 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2150 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq1 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1471 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2605 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq9 hcq5 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_1915 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2152 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1473 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2606 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq0 hcq9 hcq5 hcq8)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq0 hcq8 hcq9; omega) (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq5; omega) (by clear * - hcq0 hcq1 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·CF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_1216 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq10 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1798 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq3 hcq0 hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1218 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1938 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq10 hcq2 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2607 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq0 hcq10 hcq2 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_1223 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq10 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1800 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq3 h hcq0 hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1225 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1940 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq10 hcq2 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1801 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq3 h hcq0 hcq10 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1228 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1229 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_1230 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq10 hDn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1802 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq3 h hcq0 hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1232 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1941 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq10 hcq2 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1234 A.natDegree B.natDegree C.natDegree F.natDegree h hcq10 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq10; omega) (by clear * - hcq0 hcq6 hcq10; omega) (by clear * - hcq0 hcq3 hcq6 hcq10; omega) (by clear * - hcq0 hcq10; omega) (by clear * - hcq2; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq10; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq10; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
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
/-- Chamber `BCEFG` / `BF·CF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCEFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq4 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1803 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1804 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1805 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1806 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2608 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hcq10 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1807 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq2 h hcq0 hcq1 hcq10)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1808 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1809 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1810 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq2 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1811 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2609 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hcq10 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1812 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq10)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq5 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·CF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1813 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq1 hcq4 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1235 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1942 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq10 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2610 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq4 h hcq0 hcq10 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1815 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 hcq4 h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1237 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1944 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq10 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1816 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 hcq4 h hcq0 hcq10)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq4 hcq10; omega) (by clear * - hcq0 hcq10; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCEFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1713 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1817 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq4 hcq9 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1818 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1819 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2157 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq9 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2611 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq4 hcq1 h hcq9 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1822 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1715 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1823 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq4 hcq9 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1824 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1825 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2159 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq9 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1827 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq2 hcq4 h hcq9 hcq0)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1828 A.natDegree B.natDegree F.natDegree hcq9 h)
      · exact Or.inr (astra4u_Round4Package_nat_1829 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1830 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq4 hcq9 hcq0 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1831 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1832 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2161 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq9 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1834 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq4 hcq9 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq9; omega) (by clear * - hcq2 hcq9; omega) (by clear * - hcq0 hcq2 hcq4 hcq9; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq2 hcq9; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq2 hcq4 hcq9; omega) (by clear * - hcq2 hcq9; omega) (by clear * - hcq4 hcq9; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq2 hcq4 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9 hApos; omega)) (Or.inr (by clear * - hcq2 hcq9 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCEFG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1404 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1835 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq1 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1405 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1406 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2163 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq11 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1836 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq1 h hcq0 hcq11)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1408 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1837 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq1 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1409 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1410 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2164 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq11 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1838 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq4 hcq1 hcq0 hcq11)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq1 hcq4 hcq11; omega) (by clear * - hcq1 hcq6 hcq11; omega) (by clear * - hcq1 hcq4 hcq11; omega) (by clear * - hcq0 hcq1 hcq4 hcq11; omega) (by clear * - hcq0 hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1412 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq4 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1474 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2612 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq2 hcq4 hcq1 h hcq9)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1414 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 hcq4 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1476 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1840 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos hcq0 hcq2 hcq4 h hcq9)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq2 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq2 hcq9; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BG·CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG28810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG28810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq6 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1273 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1274 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1887 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq5 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1946 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq8 hcq9 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1278 A.natDegree B.natDegree C.natDegree G.natDegree h hcq8 hcq9 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2613 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq8 h hcq9 hcq0 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1280 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1281 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1889 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq5 h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1948 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq8 hcq9 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1285 A.natDegree B.natDegree C.natDegree G.natDegree h hcq8 hcq9 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2614 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq8 h hcq9 hcq0 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1287 A.natDegree B.natDegree C.natDegree G.natDegree hcq9 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1288 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1891 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq5 h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1950 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq8 h hcq9 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1292 A.natDegree B.natDegree C.natDegree G.natDegree h hcq8 hcq9 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1951 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq8 hcq9 hcq0 hcq2)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq9; omega) (by clear * - hcq0 hcq8 hcq9; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq8 hcq9 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq8 hcq9; omega)) (Or.inr (by clear * - hcq8 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq9 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BG·CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG32810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG32810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq4 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2615 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq1 hcq9 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2616 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq1 hcq9 hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2617 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq9 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2618 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq9 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2619 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq9 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2620 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos hcq2 h hcq1 hcq9 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq9; omega) (by clear * - hcq0 hcq1 hcq2 hcq9; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq1 hcq2 hcq5 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq1 hcq2 hcq5; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BG·CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG33810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG33810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq4 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1273 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1274 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1887 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree h hcq6 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1952 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1294 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq9 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2621 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 h hcq1 hcq9 hcq0 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1280 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1281 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1889 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq6 h hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1954 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1296 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq9 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2622 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq6 h hcq1 hcq9 hcq0 hcq3)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq9; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq6 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BG·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCEFG34810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG34810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq2 hcq3 hcq4 hcq5 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1894 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1431 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1432 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2166 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq0 hcq9 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1434 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2623 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq5 h hcq0 hcq9 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1896 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1438 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1439 A.natDegree B.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2168 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq5 hcq0 hcq9 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1441 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2624 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq3 hcq5 h hcq0 hcq9 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1443 A.natDegree B.natDegree E.natDegree G.natDegree hcq0 hcq9 h)
      · exact Or.inr (astra4u_Round4Package_nat_1898 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1445 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq0 hcq9 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1446 A.natDegree B.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2170 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hcq0 hcq9 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1448 A.natDegree B.natDegree E.natDegree G.natDegree h hcq5 hcq0 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2625 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq5 hcq0 hcq9 hcq4)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq3 hcq9; omega) (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq3 hcq9; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq9; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BG·EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCEFG36810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG36810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq5 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1894 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1449 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2172 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1450 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2626 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq1 h hcq0 hcq9 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1896 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq5 h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1452 A.natDegree B.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2174 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1453 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2627 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq1 h hcq0 hcq9 hcq6)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCEFG37810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG37810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1477 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 h hcq9 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1956 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 hcq0 h hcq9 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2176 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq6 hcq0 hcq9 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1478 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1479 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2628 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hApos hcq3 hcq6 h hcq0 hcq9)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq9; omega) (by clear * - hcq3 hcq9; omega) (by clear * - hcq0 hcq3 hcq9; omega) (by clear * - hcq9; omega) (by clear * - hcq0 hcq3 hcq8 hcq9; omega) (by clear * - hcq8 hcq9; omega) (by clear * - hcq3 hcq6 hcq9; omega) (by clear * - hcq3 hcq9; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq6 hcq8 hcq9; omega) (by clear * - hcq3 hcq9; omega) (by clear * - hcq0 hcq3 hcq6 hcq9; omega) hbl' (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq8 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq8 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq8 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq8 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq8 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCEFG38810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG38810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hDn hcq0 hcq7 hcq9 hApos hcq10 hcq15 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1241 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1242 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq10 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1841 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hAC hcq10 hcq2 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1243 A.natDegree B.natDegree C.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1958 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hAC hcq10 hcq2 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2629 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAC h hcq10 hcq15 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq10 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1245 A.natDegree B.natDegree C.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1300 A.natDegree B.natDegree C.natDegree G.natDegree h hAC hcq10 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1843 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq10 hcq2 hcq15)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq10 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq10)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq10 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1247 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1301 A.natDegree B.natDegree C.natDegree G.natDegree h hAC hcq10 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1248 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq10 hcq0)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq10; omega) (by clear * - hAC hcq10; omega) (by clear * - hcq0; omega) (by clear * - hcq10 hcq15; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq3 hApos hcq10; omega)) hbdelta' (Or.inr (by clear * - hcq4 hApos hcq10; omega)) (Or.inr (by clear * - hApos hcq10; omega)) (Or.inr (by clear * - hApos hcq10; omega)) (Or.inr (by clear * - hApos hcq10; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

end QuarticChamberKills810

end Max11DegreeRoutes
