import Grok810ScaleZeroQuarticChamberDefs1Scratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Part101Scratch

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
/-- Chamber `BEF` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEF2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEF2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hGn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hGz (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEF` / `BF·EE·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBEF4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEF4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hGn hcq0 hcq1 hcq2 hApos hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hGn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hGn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hGn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hDn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hDn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hGz hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEF` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEF8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEF8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hGn hcq0 hcq1 hcq2 hcq4 hApos hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hGz (by clear * - hcq4; omega) (by clear * - hcq1; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBEG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hDn hFn hcq0 hcq1 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq4; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn; omega)
      · exact Or.inr (by clear * - h hAB hcq4; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hDn hcq0; omega)
    · exact Or.inr (by clear * - h hAB hFn hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hAB hFn hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hAB hDn hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAB hAC hCn; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAB hDn hApos; omega)
    · exact Or.inr (by clear * - h hCn hDn hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hDn hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hFz (by clear * - hcq0; omega) hzl hzbeta hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBEG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hFn hcq0 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hCn hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hFn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hFn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hCn hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hFn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq2 hcq3; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hFz (by clear * - hcq3; omega) hzl hzbeta hzdelta hzzeta (Or.inr (by clear * - hcq2 hcq3; omega)) (Or.inr (by clear * - hcq3; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEG` / `BG·EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hFn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hCn hFn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hFz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEG` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hFn hcq0 hcq1 hcq4 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hCn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hCn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hFn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq4; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hFz (by clear * - hcq4; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq4; omega)) (Or.inr (by clear * - hcq0 hcq4; omega)) (Or.inr (by clear * - hcq4; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BFG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hDn hEn hcq0 hcq1 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hAE hCn hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq1; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hAE hCn hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq1; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hDn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAE hCn hEn; omega)
      · exact Or.inr (by clear * - h hAB hDn hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn; omega)
      · exact Or.inr (by clear * - h hAB hAE hEn; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hDn hcq1; omega)
    · exact Or.inr (by clear * - h hAB hEn hcq0; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAB hCn hEn hApos; omega)
    · exact Or.inr (by clear * - h hAB hDn hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hAB hEn hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq0; omega)
    · exact Or.inr (by clear * - h hAB hAC hCn; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAB hCn hEn hApos; omega)
    · exact Or.inr (by clear * - h hAB hDn hApos; omega)
    · exact Or.inr (by clear * - h hCn hDn hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hAB hEn hApos; omega)
    · exact Or.inr (by clear * - h hCn hDn hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    · exact Or.inr (by clear * - h hDn hApos; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1; omega)) hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BFG` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hEn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq2; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz (by clear * - hcq0 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BFG` / `BF·BG·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hEn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hEn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz (by clear * - hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BFG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBFG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hEn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq3 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq2 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hCn hEn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hEn hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hEn hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hDn hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hEn hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq2 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq3 hcq4; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq4; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq3 hcq4; omega)) (Or.inr (by clear * - hcq4; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDE` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDE3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDE3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hFn hGn hcq0 hcq2 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq4 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq4 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hGn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hGz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hApos hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
