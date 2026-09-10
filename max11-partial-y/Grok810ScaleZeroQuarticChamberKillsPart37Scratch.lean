import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart1Scratch

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
/-- Chamber `BCEFG` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCEFG40810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG40810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7 hcq13; omega)
      · exact absurd h (by clear * - hDn hcq7 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq7 hcq13; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact absurd h (by clear * - hDn hcq7 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hApos hcq13; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact absurd h (by clear * - hDn hcq7 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos hcq13; omega)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq7 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq5 hcq13; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq7 hApos hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq5 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq7 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq7 hcq13; omega)) (Or.inr (by clear * - hcq0 hApos hcq13; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CF·CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG41810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG41810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq6 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7 hcq14; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7 hcq14; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hcq14; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq0 hcq2 hcq7 hcq14; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hcq4 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq7 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq14; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CF·CG·FF·FG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG46810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq4 hcq6 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq7 hcq14; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq5 hcq7 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq1 hcq7; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq7 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq7 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCEFG47810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG47810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq12 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq12 hcq14; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq12; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq1 hcq12; omega) (by clear * - hcq0 hcq1 hcq4 hcq12; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq4 hcq12; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq12 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq12; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCEFG49810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG49810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq5 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7 hcq12 hcq14; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq3 hcq12; omega) (by clear * - hcq0 hcq1 hcq3 hcq12; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hcq12; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq1 hcq7; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos hcq12; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCEFG50810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG50810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq3 hcq4 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq14; omega)
      · exact Or.inr (by clear * - h hcq7 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq12 hcq14; omega)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq12; omega) (by clear * - hcq0 hcq1 hcq5 hcq12; omega) (by clear * - hcq12; omega) (by clear * - hcq0 hcq1 hcq7 hcq12; omega) (by clear * - hcq12; omega) (by clear * - hcq0 hcq5 hcq14; omega) (by clear * - hcq0 hcq5 hcq7; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG51810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG51810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq4 hcq8 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq5 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq5 hcq8 hcq14; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq5 hcq8 hcq14; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq14; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq8 hcq14; omega) (by clear * - hcq0; omega) (by clear * - hcq1 hcq5 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq8 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq5 hcq8 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq8 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq8 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq8 hcq14; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG53810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG53810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq2 hcq3 hcq4 hcq5 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq14; omega)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq14; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq2 hcq5 hcq14; omega) (by clear * - hcq2 hcq14; omega) (by clear * - hcq0 hcq2 hcq5 hcq14; omega) (by clear * - hcq0 hcq2 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq3 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq14; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG55810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG55810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq4 hcq5 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hApos hcq14; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq1 hcq4 hcq14; omega) (by clear * - hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq5; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos hcq14; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG56810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG56810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq3 hcq4 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq14; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq14; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq2 hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq1; omega) (by clear * - hcq2 hcq6 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq6; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCEFG57810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG57810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq4 hcq5 hcq11 hcq15 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAE hcq0 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq4 hcq10 hcq14 hcq15; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hAE hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAE hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hcq4 hcq5 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq5 hcq11 hcq15; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq10 hcq14; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hApos hcq11; omega)
      · exact Or.inr (by clear * - h hAE hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hcq5 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos hcq11 hcq15; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq10 hcq14; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hApos hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAE hcq5 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos hcq10 hcq14; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq10; omega) (by clear * - hcq11; omega) (by clear * - hcq0; omega) (by clear * - hcq11; omega) (by clear * - hcq14; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq5 hcq9 hApos hcq10 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq9 hApos hcq11; omega)) (Or.inr (by clear * - hcq9 hcq11; omega)) (Or.inr (by clear * - hApos hcq10; omega)) (Or.inr (by clear * - hcq9 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberBCEFG60810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG60810 A B C D E F G)
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
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq5 hcq6 hApos hcq10 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11 hcq15; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq11 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq11 hcq15; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq11 hcq15; omega)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11 hcq15; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq11 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq11 hcq15; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq11 hcq15; omega)
  have hrest : (xiQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq11 hcq15; omega) (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq11 hcq15; omega) (by clear * - hcq0 hcq4 hcq11 hcq15; omega) (by clear * - hcq0 hcq1 hcq15; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq3 hcq15; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq11 hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq11 hcq15; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq11 hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq11 hcq15; omega)) (Or.inr (by clear * - hcq0 hcq11 hcq15; omega))
  have hlead : (xiQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace2810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega

end QuarticChamberKills810

end Max11DegreeRoutes
