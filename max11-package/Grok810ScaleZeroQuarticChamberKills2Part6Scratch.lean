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
/-- Chamber `CDE` / `DD·DE·EE·CCC` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDE4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDE4810 A B C D E F G)
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
    exact hnc (by clear * - hBn hFn hGn hcq0 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hGz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq4 hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDF` / `CF·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDF4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDF4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hGn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hGz hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hdpos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEF` / `CF·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCEF4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hGn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hGn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hGn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hGn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq2; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hdpos; omega)) hzdelta hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CFG` / `CF·CG·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hEn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq2; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz hzl hzbeta (Or.inr (by clear * - hcq1 hApos hdpos; omega)) hzdelta hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `DEG` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberDEG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hCn hFn hcq0 hcq2 hApos hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq3 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq3; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq3 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq3; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq3 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq0 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_DEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hFz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hApos hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDE0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hFn hGn hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq3 hcq4 hcq5; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq3 hcq4 hcq5; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
      · exact Or.inr (by clear * - h hAB hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq5 hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAB hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hGn hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq2 hApos; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hcq2 hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hcq2 hApos; omega)
    · exact Or.inr (by clear * - h hcq3 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq4; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz hGz (by clear * - hcq4; omega) (by clear * - hcq3; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq3 hApos; omega)) hzdelta (Or.inr (by clear * - hcq4; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDE4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz hGz (by clear * - hcq3; omega) (by clear * - hcq4; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDE5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq1 hcq4 hcq6 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz hGz (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq1 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8; omega))
  have hlead : (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hCne hDne
  rw [degreeZeroXiQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDE7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hFn hGn hcq0 hcq2 hcq4 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq5 hcq7 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq5 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hApos hcq11; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hGn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hFn hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos hcq11; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq5 hcq11; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq9 hApos; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz hGz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq3 hcq9; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq5; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq2; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `DD·DE·EE·BBB` dies on the `ξ` face `A.natDegree + 2 * B.natDegree + E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDE8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq5; omega)
  have hrest : (xiQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest10810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz hGz (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq0 hcq2 hcq5; omega) (by clear * - hcq0 hcq2 hcq3 hcq5; omega) (by clear * - hcq0 hcq2 hcq5; omega) (by clear * - hcq2 hcq3; omega) (by clear * - hcq0 hcq2 hcq3 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq5; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq5; omega))
  have hlead : (xiQuarticChamberFace10810 A B C D E F G).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberFace10810_natDegree A B C D E F G hAne hBne hEne
  rw [degreeZeroXiQuartic810_eq_face10_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `DD·DE·EE·CCC` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDE10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq2 hcq3 hcq5 hcq10 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq11; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq11; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz hGz (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq0 hcq2 hcq4 hcq11; omega) (by clear * - hcq0 hcq2 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq11; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq11; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDE12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hGn hcq0 hcq1 hcq3 hcq4 hcq5 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz hGz (by clear * - hcq3; omega) (by clear * - hcq5; omega) (by clear * - hcq1; omega) (by clear * - hcq5; omega) (by clear * - hcq0 hcq1 hcq3 hcq5; omega) (by clear * - hcq0 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
