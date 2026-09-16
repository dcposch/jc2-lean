import Grok810ScaleZeroQuarticChamberDefs1Scratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Part101Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch

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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG14810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * B + 2 * G < A + 4 * D)
    (hcq2 : 2 * E < A + 2 * D)
    (hcq3 : 2 * G < 3 * A + 2 * D)
    (hcq7 : 4 * B < A + 2 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + 2 * D ∧ 3 * A + D < A + 2 * D ∧ A + 3 * B < A + 2 * D ∧ A + B + E < A + 2 * D ∧ 2 * B + D < A + 2 * D ∧ B + G < A + 2 * D ∧ D + E < A + 2 * D) := by
  have hbls : q ∨ (4 * A + B < A + 2 * D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAF hCn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG14810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * B + 2 * G < A + 4 * D)
    (hcq2 : 2 * E < A + 2 * D)
    (hcq3 : 2 * G < 3 * A + 2 * D)
    (hcq7 : 4 * B < A + 2 * D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + 2 * D ∧ 2 * A + D < A + 2 * D ∧ 3 * B < A + 2 * D ∧ B + E < A + 2 * D) := by
  have hbbetas : q ∨ (3 * A + B < A + 2 * D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG14810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * B + 2 * G < A + 4 * D)
    (hcq2 : 2 * E < A + 2 * D)
    (hcq7 : 4 * B < A + 2 * D)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < A + 2 * D ∧ A + D < A + 2 * D) := by
  have hbdeltas : q ∨ (2 * A + B < A + 2 * D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hFn hcq0 hcq1 hcq2 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq2 hcq3 hcq7 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEG14810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAF hCn hcq0 hcq1 hcq2 hcq3 hcq7 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEG14810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAF hCn hcq0 hcq1 hcq2 hcq3 hcq7 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEG14810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hFn hcq0 hcq1 hcq2 hcq7 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq7; omega) (by clear * - hcq2 hcq7; omega) (by clear * - hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG16810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq4 : E + G < 2 * A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < D + E ∧ 2 * A + 2 * B < D + E ∧ 2 * A + E < D + E ∧ A + B + D < D + E ∧ A + G < D + E ∧ 2 * D < D + E) := by
  have hbls : q ∨ (5 * A < D + E) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hFn hcq0 hcq4 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq4 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG16810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq4 : E + G < 2 * A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < D + E ∧ A + 2 * B < D + E ∧ A + E < D + E ∧ B + D < D + E ∧ G < D + E) := by
  have hbbetas : q ∨ (4 * A < D + E) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hFn hcq0 hcq4 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq4 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG16810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq4 : E + G < 2 * A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hnbdelta : q ∨
      4 * A ≤ D + G ∨
      4 * A ≤ E + F ∨
      3 * A ≤ 2 * B + D ∨
      4 * A ≤ 2 * B + F ∨
      4 * A ≤ B + C + E ∨
      4 * A ≤ B + 2 * D ∨
      4 * A ≤ 2 * C + D ∨
      4 * A ≤ 3 * B + C ∨
      4 * A ≤ B + E ∨
      4 * A ≤ C + D ∨
      4 * A ≤ 3 * B) :
    q ∨ (3 * A < D + E ∧ 2 * B < D + E ∧ E < D + E) := by
  have hbdeltas : q ∨ (3 * A < D + E) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAC hAD hApos hCn hFn hcq0 hcq4 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq8 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG16810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq4 : E + G < 2 * A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hnbzeta : q ∨
      3 * A ≤ D + G ∨
      3 * A ≤ E + F ∨
      2 * A ≤ 2 * B + D ∨
      3 * A ≤ 2 * B + F ∨
      3 * A ≤ B + C + E ∨
      3 * A ≤ B + 2 * D ∨
      3 * A ≤ 2 * C + D ∨
      3 * A ≤ 3 * B + C ∨
      3 * A ≤ B + E ∨
      3 * A ≤ C + D ∨
      A ≤ B ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A < D + E) := by
  rcases hnbzeta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hAC hAD hApos hCn hFn hcq0 hcq4 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hFn hcq0 hcq2 hcq6 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEG16810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hFn hcq0 hcq4 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEG16810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hFn hcq0 hcq4 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEG16810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hCn hFn hcq0 hcq4 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEG16810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hCn hFn hcq0 hcq4 hcq8 hnbzeta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq2; omega) hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq8; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq6 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq6; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG17810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : 2 * B + 2 * G < A + 4 * D)
    (hcq5 : E + G < 2 * A + 2 * D)
    (hcq7 : 4 * B < A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + D < A + 2 * B + E ∧ 2 * A + 3 * B < A + 2 * B + E ∧ 2 * A + B + E < A + 2 * B + E ∧ A + 2 * B + D < A + 2 * B + E ∧ A + D + E < A + 2 * B + E ∧ B + 2 * D < A + 2 * B + E ∧ D + G < A + 2 * B + E) := by
  have hbls : q ∨ (4 * A + D < A + 2 * B + E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAF hCn hcq0 hcq2 hcq3 hcq5 hcq7 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG17810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : 2 * B + 2 * G < A + 4 * D)
    (hcq5 : E + G < 2 * A + 2 * D)
    (hcq7 : 4 * B < A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + D < A + 2 * B + E ∧ A + 3 * B < A + 2 * B + E ∧ A + B + E < A + 2 * B + E ∧ 2 * B + D < A + 2 * B + E ∧ D + E < A + 2 * B + E) := by
  have hbbetas : q ∨ (3 * A + D < A + 2 * B + E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAF hCn hcq0 hcq2 hcq3 hcq5 hcq7 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG17810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : 2 * B + 2 * G < A + 4 * D)
    (hcq5 : E + G < 2 * A + 2 * D)
    (hcq7 : 4 * B < A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + D < A + 2 * B + E ∧ 3 * B < A + 2 * B + E ∧ B + E < A + 2 * B + E) := by
  have hbdeltas : q ∨ (2 * A + D < A + 2 * B + E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hFn hcq0 hcq2 hcq3 hcq5 hcq7 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `DD·DE·EE·BBB` dies on the `ξ` face `A.natDegree + 2 * B.natDegree + E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG17810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hFn hcq0 hcq2 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEG17810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAF hCn hcq0 hcq2 hcq3 hcq5 hcq7 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEG17810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAF hCn hcq0 hcq2 hcq3 hcq5 hcq7 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEG17810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hFn hcq0 hcq2 hcq3 hcq5 hcq7 hcq8 hkbdelta
  have hrest : (xiQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest10810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq0 hcq2 hcq3 hcq8; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq2 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega))
  have hlead : (xiQuarticChamberFace10810 A B C D E F G).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberFace10810_natDegree A B C D E F G hAne hBne hEne
  rw [degreeZeroXiQuartic810_eq_face10_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG20810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + 2 * B + 2 * G < 4 * E)
    (hcq2 : A + 2 * D < 2 * E)
    (hcq5 : G < A + E)
    (hcq8 : 2 * B < E)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < 2 * E ∧ 3 * A + D < 2 * E ∧ A + 3 * B < 2 * E ∧ A + B + E < 2 * E ∧ 2 * B + D < 2 * E ∧ B + G < 2 * E ∧ D + E < 2 * E) := by
  have hbls : q ∨ (4 * A + B < 2 * E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAF hCn hcq0 hcq1 hcq2 hcq5 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG20810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + 2 * B + 2 * G < 4 * E)
    (hcq2 : A + 2 * D < 2 * E)
    (hcq5 : G < A + E)
    (hcq8 : 2 * B < E)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < 2 * E ∧ 2 * A + D < 2 * E ∧ 3 * B < 2 * E ∧ B + E < 2 * E) := by
  have hbbetas : q ∨ (3 * A + B < 2 * E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq2 hcq5 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG20810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + 2 * B + 2 * G < 4 * E)
    (hcq2 : A + 2 * D < 2 * E)
    (hcq5 : G < A + E)
    (hcq8 : 2 * B < E)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < 2 * E ∧ A + D < 2 * E) := by
  have hbdeltas : q ∨ (2 * A + B < 2 * E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hFn hcq0 hcq1 hcq2 hcq5 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq2 hcq4 hcq8 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEG20810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAF hCn hcq0 hcq1 hcq2 hcq5 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEG20810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAF hCn hcq0 hcq1 hcq2 hcq5 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEG20810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hFn hcq0 hcq1 hcq2 hcq5 hcq8 hkbdelta
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq8; omega) (by clear * - hcq2; omega) (by clear * - hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAE : E < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq5 : 4 * F < 5 * A + 6 * B)
    (hcq8 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ A + B + D < A + 3 * B ∧ A + G < A + 3 * B ∧ B + F < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAE hApos hCn hEn hcq0 hcq1 hcq5 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAE : E < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq5 : 4 * F < 5 * A + 6 * B)
    (hcq8 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ B + D < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAE hApos hCn hEn hcq0 hcq1 hcq5 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq8 : D < A + B)
    (hnbdelta : q ∨
      4 * A ≤ D + G ∨
      4 * A ≤ E + F ∨
      3 * A ≤ 2 * B + D ∨
      4 * A ≤ 2 * B + F ∨
      4 * A ≤ B + C + E ∨
      4 * A ≤ B + 2 * D ∨
      4 * A ≤ 2 * C + D ∨
      4 * A ≤ 3 * B + C ∨
      4 * A ≤ B + E ∨
      4 * A ≤ C + D ∨
      4 * A ≤ 3 * B) :
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAC hAE hApos hCn hEn hcq0 hcq1 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq8 : D < A + B)
    (hnbzeta : q ∨
      3 * A ≤ D + G ∨
      3 * A ≤ E + F ∨
      2 * A ≤ 2 * B + D ∨
      3 * A ≤ 2 * B + F ∨
      3 * A ≤ B + C + E ∨
      3 * A ≤ B + 2 * D ∨
      3 * A ≤ 2 * C + D ∨
      3 * A ≤ 3 * B + C ∨
      3 * A ≤ B + E ∨
      3 * A ≤ C + D ∨
      A ≤ B ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A < A + 3 * B) := by
  rcases hnbzeta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hAC hApos hCn hEn hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq8 : D < A + B)
    (hnbtheta : q ∨
      2 * A ≤ D + G ∨
      2 * A ≤ E + F ∨
      A ≤ 2 * B + D ∨
      2 * A ≤ 2 * B + F ∨
      2 * A ≤ B + C + E ∨
      2 * A ≤ B + 2 * D ∨
      2 * A ≤ 2 * C + D ∨
      2 * A ≤ 3 * B + C ∨
      2 * A ≤ B + E ∨
      2 * A ≤ C + D ∨
      2 * A ≤ 3 * B ∨
      2 * A ≤ F ∨
      2 * A ≤ B + C ∨
      2 * A ≤ D) :
    q ∨ (A < A + 3 * B) := by
  rcases hnbtheta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hApos hCn hEn hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hEn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAE hApos hCn hEn hcq0 hcq1 hcq5 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAE hApos hCn hEn hcq0 hcq1 hcq5 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAE hApos hCn hEn hcq0 hcq1 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hApos hCn hEn hcq0 hcq1 hcq8 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hEn hcq0 hcq1 hcq8 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq8; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1; omega)) hzdelta (Or.inr (by clear * - hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG2810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + B + F ∧ 3 * A + D < A + B + F ∧ A + 3 * B < A + B + F ∧ 2 * A + F < A + B + F ∧ 2 * B + D < A + B + F ∧ B + G < A + B + F) := by
  have hbls : q ∨ (4 * A + B < A + B + F) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG2810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + B + F ∧ 2 * A + D < A + B + F ∧ 3 * B < A + B + F ∧ A + F < A + B + F) := by
  have hbbetas : q ∨ (3 * A + B < A + B + F) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hCn hEn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG2810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < A + B + F ∧ A + D < A + B + F ∧ F < A + B + F) := by
  have hbdeltas : q ∨ (2 * A + B < A + B + F) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG2810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq3 hcq5 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG2810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hCn hEn hcq0 hcq1 hcq3 hcq5 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG2810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq3 hcq5 hkbdelta
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq5; omega) (by clear * - hcq2; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG4810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + B + F ∧ 3 * A + D < A + B + F ∧ A + 3 * B < A + B + F ∧ 2 * A + F < A + B + F ∧ 2 * B + D < A + B + F ∧ B + G < A + B + F) := by
  have hbls : q ∨ (4 * A + B < A + B + F) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG4810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + B + F ∧ 2 * A + D < A + B + F ∧ 3 * B < A + B + F ∧ A + F < A + B + F) := by
  have hbbetas : q ∨ (3 * A + B < A + B + F) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hCn hEn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq1 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG4810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < A + B + F ∧ A + D < A + B + F ∧ F < A + B + F) := by
  have hbdeltas : q ∨ (2 * A + B < A + B + F) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·BG·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG4810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq3 hcq5 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG4810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hCn hEn hcq0 hcq1 hcq3 hcq5 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG4810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq3 hcq5 hkbdelta
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq1 hcq5; omega) (by clear * - hcq2; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG5810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : B + F = 2 * D)
    (hcq2 : D < A + B)
    (hcq7 : A + 4 * B < 2 * F)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 2 * A + 2 * B < B + G ∧ A + B + D < B + G ∧ A + G < B + G ∧ B + F < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG5810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : B + F = 2 * D)
    (hcq2 : D < A + B)
    (hcq7 : A + 4 * B < 2 * F)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ A + 2 * B < B + G ∧ B + D < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG5810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : B + F = 2 * D)
    (hcq2 : D < A + B)
    (hcq7 : A + 4 * B < 2 * F)
    (hnbdelta : q ∨
      4 * A ≤ D + G ∨
      4 * A ≤ E + F ∨
      3 * A ≤ 2 * B + D ∨
      4 * A ≤ 2 * B + F ∨
      4 * A ≤ B + C + E ∨
      4 * A ≤ B + 2 * D ∨
      4 * A ≤ 2 * C + D ∨
      4 * A ≤ 3 * B + C ∨
      4 * A ≤ B + E ∨
      4 * A ≤ C + D ∨
      4 * A ≤ 3 * B) :
    q ∨ (3 * A < B + G ∧ 2 * B < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG5810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : B + F = 2 * D)
    (hcq2 : D < A + B)
    (hcq7 : A + 4 * B < 2 * F)
    (hnbzeta : q ∨
      3 * A ≤ D + G ∨
      3 * A ≤ E + F ∨
      2 * A ≤ 2 * B + D ∨
      3 * A ≤ 2 * B + F ∨
      3 * A ≤ B + C + E ∨
      3 * A ≤ B + 2 * D ∨
      3 * A ≤ 2 * C + D ∨
      3 * A ≤ 3 * B + C ∨
      3 * A ≤ B + E ∨
      3 * A ≤ C + D ∨
      A ≤ B ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A < B + G) := by
  rcases hnbzeta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·BG·DD` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG5810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq7 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG5810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq7 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG5810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq7 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG5810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq2 hcq7 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq7; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG6810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : B + F = 2 * D)
    (hcq2 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + D < A + D + F ∧ 2 * A + 3 * B < A + D + F ∧ 3 * A + F < A + D + F ∧ A + 2 * B + D < A + D + F ∧ 2 * B + F < A + D + F ∧ B + 2 * D < A + D + F ∧ D + G < A + D + F) := by
  have hbls : q ∨ (4 * A + D < A + D + F) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG6810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : B + F = 2 * D)
    (hcq2 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + D < A + D + F ∧ A + 3 * B < A + D + F ∧ 2 * A + F < A + D + F ∧ 2 * B + D < A + D + F) := by
  have hbbetas : q ∨ (3 * A + D < A + D + F) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG6810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : B + F = 2 * D)
    (hcq2 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + D < A + D + F ∧ 3 * B < A + D + F ∧ A + F < A + D + F) := by
  have hbdeltas : q ∨ (2 * A + D < A + D + F) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·BG·DD·BBB` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG6810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG6810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDFG6810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hkbdelta
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq1 hcq2 hcq3; omega) (by clear * - hcq1 hcq2 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq3; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG10810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ A + B + D < A + 3 * B ∧ A + G < A + 3 * B ∧ B + F < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG10810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ B + D < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG10810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hnbdelta : q ∨
      4 * A ≤ D + G ∨
      4 * A ≤ E + F ∨
      3 * A ≤ 2 * B + D ∨
      4 * A ≤ 2 * B + F ∨
      4 * A ≤ B + C + E ∨
      4 * A ≤ B + 2 * D ∨
      4 * A ≤ 2 * C + D ∨
      4 * A ≤ 3 * B + C ∨
      4 * A ≤ B + E ∨
      4 * A ≤ C + D ∨
      4 * A ≤ 3 * B) :
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG10810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hnbzeta : q ∨
      3 * A ≤ D + G ∨
      3 * A ≤ E + F ∨
      2 * A ≤ 2 * B + D ∨
      3 * A ≤ 2 * B + F ∨
      3 * A ≤ B + C + E ∨
      3 * A ≤ B + 2 * D ∨
      3 * A ≤ 2 * C + D ∨
      3 * A ≤ 3 * B + C ∨
      3 * A ≤ B + E ∨
      3 * A ≤ C + D ∨
      A ≤ B ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A < A + 3 * B) := by
  rcases hnbzeta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG10810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : D < A + B)
    (hnbtheta : q ∨
      2 * A ≤ D + G ∨
      2 * A ≤ E + F ∨
      A ≤ 2 * B + D ∨
      2 * A ≤ 2 * B + F ∨
      2 * A ≤ B + C + E ∨
      2 * A ≤ B + 2 * D ∨
      2 * A ≤ 2 * C + D ∨
      2 * A ≤ 3 * B + C ∨
      2 * A ≤ B + E ∨
      2 * A ≤ C + D ∨
      2 * A ≤ 3 * B ∨
      2 * A ≤ F ∨
      2 * A ≤ B + C ∨
      2 * A ≤ D) :
    q ∨ (A < A + 3 * B) := by
  rcases hnbtheta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·DD·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG10810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG10810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG10810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG10810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDFG10810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq3; omega) (by clear * - hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq3; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG13810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hcq6 : 2 * G < 5 * A + 2 * B)
    (hcq7 : A + 2 * B < G)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 2 * A + 2 * B < B + G ∧ A + B + D < B + G ∧ A + G < B + G ∧ B + F < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq3 hcq5 hcq6 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq5 hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG13810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hcq6 : 2 * G < 5 * A + 2 * B)
    (hcq7 : A + 2 * B < G)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ A + 2 * B < B + G ∧ B + D < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq3 hcq5 hcq6 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG13810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hcq6 : 2 * G < 5 * A + 2 * B)
    (hcq7 : A + 2 * B < G)
    (hnbdelta : q ∨
      4 * A ≤ D + G ∨
      4 * A ≤ E + F ∨
      3 * A ≤ 2 * B + D ∨
      4 * A ≤ 2 * B + F ∨
      4 * A ≤ B + C + E ∨
      4 * A ≤ B + 2 * D ∨
      4 * A ≤ 2 * C + D ∨
      4 * A ≤ 3 * B + C ∨
      4 * A ≤ B + E ∨
      4 * A ≤ C + D ∨
      4 * A ≤ 3 * B) :
    q ∨ (3 * A < B + G ∧ 2 * B < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq3 hcq5 hcq6 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG13810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq3 : D < A + B)
    (hcq5 : F < 2 * A + B)
    (hcq6 : 2 * G < 5 * A + 2 * B)
    (hcq7 : A + 2 * B < G)
    (hnbzeta : q ∨
      3 * A ≤ D + G ∨
      3 * A ≤ E + F ∨
      2 * A ≤ 2 * B + D ∨
      3 * A ≤ 2 * B + F ∨
      3 * A ≤ B + C + E ∨
      3 * A ≤ B + 2 * D ∨
      3 * A ≤ 2 * C + D ∨
      3 * A ≤ 3 * B + C ∨
      3 * A ≤ B + E ∨
      3 * A ≤ C + D ∨
      A ≤ B ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A < B + G) := by
  rcases hnbzeta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAC hCn hEn hcq3 hcq5 hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq3 hcq4 hcq6 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG13810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq3 hcq5 hcq6 hcq7 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG13810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq3 hcq5 hcq6 hcq7 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG13810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq3 hcq5 hcq6 hcq7 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDFG13810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq3 hcq5 hcq6 hcq7 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq7; omega) (by clear * - hcq3 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq3 hcq7; omega)) hzzeta (Or.inr (by clear * - hcq6 hcq7; omega)) (Or.inr (by clear * - hcq7; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG16810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq3 : 2 * D + 2 * F < A + 2 * B + 2 * G)
    (hcq4 : D < A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + 2 * D ∧ 3 * A + D < A + 2 * D ∧ A + 3 * B < A + 2 * D ∧ 2 * A + F < A + 2 * D ∧ 2 * B + D < A + 2 * D ∧ B + G < A + 2 * D) := by
  have hbls : q ∨ (4 * A + B < A + 2 * D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq3 hcq4; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG16810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq3 : 2 * D + 2 * F < A + 2 * B + 2 * G)
    (hcq4 : D < A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + 2 * D ∧ 2 * A + D < A + 2 * D ∧ 3 * B < A + 2 * D ∧ A + F < A + 2 * D) := by
  have hbbetas : q ∨ (3 * A + B < A + 2 * D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq1 hcq3 hcq4; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG16810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq3 : 2 * D + 2 * F < A + 2 * B + 2 * G)
    (hcq4 : D < A + B)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < A + 2 * D ∧ A + D < A + 2 * D ∧ F < A + 2 * D) := by
  have hbdeltas : q ∨ (2 * A + B < A + 2 * D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BG·DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDFG16810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hcq4 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDFG16810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hcq4 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDFG16810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hcq4 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
