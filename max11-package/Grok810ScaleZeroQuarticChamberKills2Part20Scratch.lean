import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Part1Scratch

/-! # Cost-ladder chamber kills, `(8,10)` scale zero

265 further single-monomial chamber kills.  Untracked note.
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

section QuarticChamberKills2810

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq4 hcq7 hcq8 hcq10 hcq11 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq4 hcq7 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq4 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq4 hcq10 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hcq7 hcq9 hcq10 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq4 hcq7 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq4 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq4 hcq10 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hcq7 hcq10 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq7 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq4 hcq9 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq7 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq4 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq10 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq7 hcq10 hcq11; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hcq6; omega)
    · exact Or.inr (by clear * - h hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hcq9 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq7 hcq10 hcq11; omega)
    · exact Or.inr (by clear * - h hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq4 hcq9 hcq10 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq10 hcq11; omega)
    · exact Or.inr (by clear * - h hcq7 hcq10 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq4 hcq10 hcq11; omega)
    · exact Or.inr (by clear * - h hcq10 hcq11; omega)
    · exact Or.inr (by clear * - h hcq9 hcq10 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq10 hcq11; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq11; omega) (by clear * - hcq4 hcq11; omega) (by clear * - hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq4 hcq11; omega)) hzzeta (Or.inr (by clear * - hcq10 hcq11; omega)) (Or.inr (by clear * - hcq11; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG28810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG28810 A B C D E F G)
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
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq5; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq5; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq3 hcq5; omega) (by clear * - hcq0 hcq2 hcq5; omega) (by clear * - hcq0 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BG·EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG34810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG34810 A B C D E F G)
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
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq6 hcq7 hcq8 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq7 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7 hcq8; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq6 hcq7 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq6 hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7 hcq8; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq7 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq6 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq8; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq7 hcq8; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq4 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG38810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG38810 A B C D E F G)
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
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq4 hcq12 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq4 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq4 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq12; omega) (by clear * - hcq1; omega) (by clear * - hcq3 hcq12; omega) (by clear * - hcq0 hcq1 hcq12; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG42810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG42810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hcq0 hcq2 hcq3 hcq4 hcq11 hcq12 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hAB hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq0 hApos hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq4 hcq7 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hAB hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq0 hApos hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq7 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq13; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hApos hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hApos hcq13; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hApos hcq13; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAD hcq0 hcq13; omega)
    · exact Or.inr (by clear * - h hAD hcq0 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq13; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq13; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq11; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD·DE·EE·BBB` dies on the `ξ` face `A.natDegree + 2 * B.natDegree + E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG43810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG43810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq2 hcq3 hcq4 hcq5 hcq12 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq5 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq13; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq5 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq5 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq13; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq5 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq13; omega)
  have hrest : (xiQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest10810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq2 hcq13; omega) (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq0 hcq2 hcq4 hcq13; omega) (by clear * - hcq0 hcq2 hcq13; omega) (by clear * - hcq2 hcq4; omega) (by clear * - hcq0 hcq2 hcq3 hcq13; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq13; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq4 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq13; omega))
  have hlead : (xiQuarticChamberFace10810 A B C D E F G).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberFace10810_natDegree A B C D E F G hAne hBne hEne
  rw [degreeZeroXiQuartic810_eq_face10_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG48810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG48810 A B C D E F G)
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
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq7 hcq12 hcq13 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq8 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq8 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq13; omega) (by clear * - hcq1; omega) (by clear * - hcq3; omega) (by clear * - hcq13; omega) (by clear * - hcq0 hcq1 hcq3 hcq13; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq13; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq13; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·CG·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq4 hcq6 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq7 hcq10; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq10; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq10; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq5; omega)
    · exact Or.inr (by clear * - h hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq10; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7 hcq10; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5 hcq9; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) hzdelta (Or.inr (by clear * - hcq3; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·CG·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq5; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq5; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq5; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq3; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·CG·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq6 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq4 hcq7; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hcq4 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq2 hcq4 hcq7; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq12; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq12; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq12; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq12; omega)
    · exact Or.inr (by clear * - h hcq12; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq3; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
