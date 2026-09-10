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
/-- Chamber `BCEFG` / `CF·CG·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCEFG44810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG44810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq5; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `CF·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCEFG48810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG48810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq5 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq5 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq13; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq13; omega) (by clear * - hcq13; omega) (by clear * - hcq1 hcq4 hcq13; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq13; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq13; omega)) (Or.inr (by clear * - hcq1 hcq13; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCEFG58810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG58810 A B C D E F G)
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
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq5 hcq10 hcq11 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq10; omega) (by clear * - hcq11; omega) (by clear * - hcq1; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq10; omega) (by clear * - hcq0 hcq2 hcq10; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq10; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq10 hcq11; omega)) (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq0 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq10 hcq11; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG0810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos hcq13; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos hcq12; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq0 hcq1 hcq12 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hAB hcq0; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos hcq13; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos hcq12; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hcq1 hcq12 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq13; omega)
      · exact Or.inr (by clear * - h hcq12; omega)
      · exact Or.inr (by clear * - h hAB hCn hApos hcq12; omega)
      · exact Or.inr (by clear * - h hAB hCn; omega)
      · exact Or.inr (by clear * - h hAB hcq13; omega)
      · exact Or.inr (by clear * - h hAB hAC hCn hcq12; omega)
      · exact Or.inr (by clear * - h hAB; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hApos hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos hcq13; omega)
    · exact Or.inr (by clear * - h hcq12; omega)
    · exact Or.inr (by clear * - h hAB hCn hApos hcq12; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hApos hcq13; omega)
    · exact Or.inr (by clear * - h hAB hCn hApos hcq12; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq0; omega)
    · exact Or.inr (by clear * - h hAB hAC hCn; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hcq12; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hcq12; omega)
    · exact Or.inr (by clear * - h hAB hCn hcq12; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hcq6 hApos; omega)
    · exact Or.inr (by clear * - h hAB hCn hcq12; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAB hCn hApos; omega)
    · exact Or.inr (by clear * - h hAB hcq12; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq12; omega) (by clear * - hcq1; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1; omega)) hzdelta (Or.inr (by clear * - hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG2810 A B C D E F G)
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq4 hcq6 hcq9 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq4 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq9; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hcq9; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq9; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq6 hcq9; omega) (by clear * - hcq4; omega) (by clear * - hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·BG·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG4810 A B C D E F G)
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
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq4 hcq6 hcq9 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8 hcq9; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq4 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8 hcq9; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hcq9; omega)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq1 hcq9; omega) (by clear * - hcq2; omega) (by clear * - hcq1 hcq6 hcq9; omega) (by clear * - hcq4; omega) (by clear * - hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·BG·DD` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG5810 A B C D E F G)
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
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq11 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq11; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq3 hcq11; omega) (by clear * - hcq0 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq3 hcq11; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq11; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·BG·DD·BBB` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG6810 A B C D E F G)
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
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq4; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq4; omega)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq1 hcq2 hcq4; omega) (by clear * - hcq1 hcq2 hcq3; omega) (by clear * - hcq1 hcq2 hcq4; omega) (by clear * - hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hcq1 hcq2 hcq3 hcq4; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq1 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq3 hcq4; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq4; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·BG·EE` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG11810 A B C D E F G)
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
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq4 hcq6 hcq11 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq6 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq6 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq6 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq7 hcq11; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq11; omega) (by clear * - hcq0 hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq7 hcq11; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq11; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq7 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq11; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·DD·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG16810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq4; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq4; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG18810 A B C D E F G)
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
    exact hnc (by clear * - hCn hcq0 hcq1 hcq3 hcq4 hcq11 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
    · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq4 hcq11; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq1 hcq11; omega) (by clear * - hcq1 hcq4 hcq11; omega) (by clear * - hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq11; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq4 hcq11; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq11; omega)) (Or.inr (by clear * - hcq1 hcq11; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `BF·EE·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG22810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq5 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq5 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq5 hcq7; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq13; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq13; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq13; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq1 hcq3 hcq13; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq13; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq13; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq13; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
