import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
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
/-- Chamber `BCFG` / `BF·CF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq7; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BF·CF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hApos; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq2 hcq6; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq2 hcq6; omega) (by clear * - hcq1 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BG·CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq5 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq6; omega) (by clear * - hcq0 hcq5 hcq6; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq5 hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq6; omega)) (Or.inr (by clear * - hcq5 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BG·CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq6; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hApos; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq3 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq3 hcq5 hcq6; omega) (by clear * - hcq5 hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq3 hcq6; omega) hbl' (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hdpos hpi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hDn hEn hcq0 hcq4 hcq6 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hcq2 hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hAC hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hcq2 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hcq3 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hAC hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq7 hApos; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hAC hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq7 hApos; omega)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq7; omega) (by clear * - hAC hcq7; omega) (by clear * - hcq0; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq3 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq4 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq9; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq4 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq9 hApos; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq4 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq9 hApos; omega)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq9 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq9 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq4 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq4 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq2 hcq4 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq0 hcq2 hcq4 hcq9; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·CG·FF·FG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq4 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq5 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq1 hcq5 hcq9; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq9; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq3 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq4 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq9; omega)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq1 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq8; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG27810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq5 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq5 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq5 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq5 hcq9; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq5 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq5 hcq9; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq5 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq1 hcq9; omega) (by clear * - hcq1 hcq5 hcq9; omega) (by clear * - hcq0; omega) (by clear * - hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq9; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega

end QuarticChamberKills810

end Max11DegreeRoutes
