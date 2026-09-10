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
/-- Chamber `CEF` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hGn hcq0 hcq1 hcq3 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hdpos; omega)) (Or.inr (by clear * - hcq0 hcq1 hdpos; omega)) (Or.inr (by clear * - hdpos; omega)) (Or.inr (by clear * - hcq0 hcq3 hdpos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEF` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEF5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hGn hcq0 hcq1 hcq3 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
    · exact absurd h (by clear * - hGn hApos; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEF` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCEF6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hGn hcq0 hcq1 hcq3 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hcq0 hcq2 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEF` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEF7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hGn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hAE hcq1; omega)
      · exact Or.inr (by clear * - h hAE hcq1; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq4; omega)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hApos; omega)
    · exact Or.inr (by clear * - h hcq1 hcq4; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hcq1; omega)
    · exact absurd h (by clear * - hGn hApos; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq3; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq3; omega)) (Or.inr (by clear * - hcq3; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEF` / `EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEF9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hGn hcq0 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hAE hcq0 hcq2; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hAE hcq0; omega)
      · exact Or.inr (by clear * - h hAE hcq0; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq0 hcq2; omega)
  have hbbeta' : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hApos; omega)
    · exact Or.inr (by clear * - h hAE hcq0 hcq2; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact absurd h (by clear * - hGn hApos; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hAE hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEF` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCEF10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAC hAE hBn hDn hGn hcq0 hcq1 hcq3 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hAF hcq0; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hAF hcq1; omega)
      · exact Or.inr (by clear * - h hAF; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAF hcq0 hcq1; omega)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hAF hcq0; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hAF hcq1; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hAF hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCEG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hFn hcq0 hcq1 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by clear * - hcq0; omega) (by clear * - hcq1; omega) (Or.inr (by clear * - hcq0; omega)) (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq0; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEG` / `CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCEG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hFn hcq0 hcq3 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by clear * - hcq3; omega) (Or.inr (by clear * - hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq3; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEG` / `CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCEG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hFn hcq0 hcq3 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by clear * - hcq3; omega) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hFn hcq0 hcq3 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by clear * - hcq3; omega) (by clear * - hcq0; omega) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq3; omega)) (Or.inr (by clear * - hcq3; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEG` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCEG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hFn hcq0 hcq1 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (xiQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest2810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by clear * - hcq0 hcq1; omega) (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1; omega))
  have hlead : (xiQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace2810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCEG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hFn hcq0 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq2; omega) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega

end QuarticChamberKills810

end Max11DegreeRoutes
