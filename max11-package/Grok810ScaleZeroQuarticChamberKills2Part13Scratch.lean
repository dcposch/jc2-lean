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
/-- Chamber `CDEF` / `DD·DE·EE·CCC` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEF17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF17810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq2 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `CG·DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hFn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq6; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `CG·DD·DE·EE·CCC` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hFn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hFn hcq0 hcq2 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq8 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq4 hcq8; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq8 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq4 hcq8; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq8 hApos; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAD hFn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq4 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq8; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq6 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq4 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hApos hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `DD·DE·EE·CCC` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG17810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hFn hcq0 hcq2 hcq3 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq0 hcq2 hcq5 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq5 hcq7; omega)
    · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq5 hcq7; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq8 hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CF·CG·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq6; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CF·CG·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hdpos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CF·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hEn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq8; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq8 hdpos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq8 hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CF·CG·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCEFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq2 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq3 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq3 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq6; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3 hcq6; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq3 hcq5; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq1 hcq5; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq3 hcq5; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hzl hzbeta (Or.inr (by clear * - hcq1 hApos hdpos; omega)) hzdelta hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CF·CG·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq3; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hcq3 hdpos; omega)) hzdelta hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CF·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCEFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hDn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq3; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hdpos; omega)) hzdelta hzzeta hztheta
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEF0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hGn hcq1 hcq3 hcq5 hcq8 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq8 hcq9 hcq10; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq8 hcq9 hcq10; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq10; omega)
      · exact Or.inr (by clear * - h hAB hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq8 hApos hcq10; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hGn hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq5 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hApos hcq10; omega)
      · exact Or.inr (by clear * - h hAB hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hcq8; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq8 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hGn hcq9; omega)
    · exact Or.inr (by clear * - h hcq0 hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hcq9; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq5 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hcq9; omega)
    · exact Or.inr (by clear * - h hcq8 hcq9; omega)
    · exact Or.inr (by clear * - h hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hcq5 hApos; omega)
    · exact Or.inr (by clear * - h hcq8 hcq9 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq9; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq9; omega) (by clear * - hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq8 hApos; omega)) hzdelta (Or.inr (by clear * - hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
