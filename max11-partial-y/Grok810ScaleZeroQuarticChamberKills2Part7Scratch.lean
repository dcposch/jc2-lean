import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart1Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
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
/-- Chamber `BCDF` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDF0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hEn hGn hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq5 hcq6; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq5 hcq6; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAE hEn; omega)
      · exact Or.inr (by clear * - h hAB hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hGn hcq6; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hcq6; omega)
    · exact Or.inr (by clear * - h hcq5 hcq6; omega)
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hAB hEn hApos; omega)
    · exact Or.inr (by clear * - h hcq5 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq6; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq6; omega) (by clear * - hcq5; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hzdelta (Or.inr (by clear * - hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hGn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4 hcq5; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq5; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq2; omega) (by clear * - hcq3 hcq5; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) hzdelta (Or.inr (by clear * - hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `BF·CF·DD` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDF6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hGn hcq0 hcq1 hcq2 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq5; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq2 hcq5; omega) (by clear * - hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq5; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq5; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `BF·DD·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDF11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hGn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq3; omega) (by clear * - hcq1 hcq5; omega) (by clear * - hcq1 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq5; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq5; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq5; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `CF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDF15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hGn hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq7 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq3 hcq7 hcq9; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq3 hcq7 hcq9; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq7 hcq9; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq2 hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq3 hcq7 hcq9; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq3 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq3 hcq7 hcq9; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3 hcq7 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq7; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `CF·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDF18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hGn hcq0 hcq1 hcq2 hcq3 hApos hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq1 hcq8; omega) (by clear * - hcq1 hcq8 hcq10; omega) (by clear * - hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq8 hcq10; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq8 hcq10; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq8 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq8; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDF22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hGn hcq0 hcq1 hcq3 hcq5 hcq6 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq5; omega) (by clear * - hcq6; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq5 hcq6; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq1 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) hzdelta (Or.inr (by clear * - hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDF23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hGn hcq0 hcq1 hcq4 hcq6 hcq8 hApos hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq6 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq6 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9; omega)
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq9; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq1 hcq4 hcq9; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq1 hcq4 hcq9; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9; omega))
  have hlead : (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hCne hDne
  rw [degreeZeroXiQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hEn hFn hcq0 hcq2 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq5 hcq6; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq5 hcq6; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAE hEn; omega)
      · exact Or.inr (by clear * - h hAB hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hFn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hcq5; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hAB hEn hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq6; omega)
    · exact Or.inr (by clear * - h hEn hFn hApos; omega)
    · exact Or.inr (by clear * - h hcq6; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hEn hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hcq6; omega)
    · exact Or.inr (by clear * - h hcq5 hcq6; omega)
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hAB hEn hApos; omega)
    · exact Or.inr (by clear * - h hcq5 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq6; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz (by clear * - hcq6; omega) (by clear * - hcq5; omega) (by clear * - hcq0; omega) hzl hzbeta (Or.inr (by clear * - hcq5 hApos; omega)) hzdelta (Or.inr (by clear * - hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hFn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hEn hFn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz (by clear * - hcq4; omega) (by clear * - hcq2 hcq4; omega) (by clear * - hcq0 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq2 hcq4; omega)) hzzeta (Or.inr (by clear * - hcq3 hcq4; omega)) (Or.inr (by clear * - hcq4; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDG` / `BG·CG·DD` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hFn hcq0 hcq1 hcq2 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAF hEn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hEn hFn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz (by clear * - hcq4; omega) (by clear * - hcq2 hcq4; omega) (by clear * - hcq0 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq2 hcq4; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq4; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDG` / `BG·CG·DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hFn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz (by clear * - hcq0 hcq1 hcq2 hcq6; omega) (by clear * - hcq0 hcq1 hcq2 hcq6; omega) (by clear * - hcq0 hcq1 hcq2 hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega))
  have hlead : (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hCne hDne
  rw [degreeZeroXiQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
