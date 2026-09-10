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
/-- Chamber `BCDEFG` / `BF·DD·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG41810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG41810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq6 hcq14; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq6 hcq14; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
    · exact Or.inr (by clear * - h hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
    · exact Or.inr (by clear * - h hcq6; omega)
    · exact Or.inr (by clear * - h hcq1 hcq6 hcq14; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6; omega)
    · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq6; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq14; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq14; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG43810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG43810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hcq13 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq13; omega)
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq13; omega) (by clear * - hcq1 hcq6 hcq13; omega) (by clear * - hcq1 hcq4 hcq13; omega) (by clear * - hcq1 hcq3; omega) (by clear * - hcq1 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq13; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq6 hcq13; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq13; omega)) (Or.inr (by clear * - hcq1 hcq13; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·EE·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG47810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG47810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14 hcq16; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14 hcq16; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq16; omega)
    · exact Or.inr (by clear * - h hcq1 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
    · exact Or.inr (by clear * - h hcq1 hcq14 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq16; omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq5 hcq16; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq14; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq5 hcq14; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq14; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG50810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG50810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq2 hcq3 hcq6 hcq7 hcq10 hcq12 hcq13 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq11 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq12 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq6 hcq9 hcq11 hcq12 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq11 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq12 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq6 hcq9 hcq12 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq11 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq9 hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq12 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq9 hcq12 hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq11 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq9 hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6 hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq11 hcq12 hcq13; omega)
      · exact Or.inr (by clear * - h hcq2 hcq12 hcq13; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq12 hcq13; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq6 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq1; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hApos hcq13; omega)) hzdelta (Or.inr (by clear * - hcq6 hcq13; omega)) hzzeta (Or.inr (by clear * - hcq12 hcq13; omega)) (Or.inr (by clear * - hcq13; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·DD` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG54810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG54810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hcq13 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq6 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq13; omega)) hzdelta (Or.inr (by clear * - hcq6 hcq13; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq6 hcq13; omega)) (Or.inr (by clear * - hcq13; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG55810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG55810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq6 hcq8 hcq9 hcq10 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq7 hcq10; omega) (by clear * - hcq0 hcq1 hcq8 hcq10; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq10; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq10; omega))
  have hlead : (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hCne hDne
  rw [degreeZeroXiQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·CG·EE` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG60810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG60810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq4 hcq7 hcq8 hcq9 hcq13 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq9 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq13; omega) (by clear * - hcq1 hcq5 hcq9 hcq13; omega) (by clear * - hcq0 hcq13; omega) (by clear * - hcq3; omega) (by clear * - hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq9 hcq13; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq5 hcq9 hcq13; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq5 hcq9 hcq13; omega)) (Or.inr (by clear * - hcq13; omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG65810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG65810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hcq7 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq7; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq5 hcq7; omega) (by clear * - hcq0 hcq1 hcq4 hcq7; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq5 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq7; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG71810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG71810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq5 hcq8 hcq9 hcq10 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq10; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq10; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq10; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq4 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq6 hcq9; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq10; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG75810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG75810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq2 hcq4 hcq7 hcq10 hcq13 hcq14 hcq17 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
      · exact Or.inr (by clear * - h hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq5 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq5 hcq8 hcq10 hcq17 hcq20; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
      · exact Or.inr (by clear * - h hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq5 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq5 hcq8 hcq10 hcq17 hcq20; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
      · exact Or.inr (by clear * - h hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq5 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
      · exact Or.inr (by clear * - h hcq8 hcq10 hcq17 hcq20; omega)
      · exact Or.inr (by clear * - h hcq5 hcq10 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq8 hcq10 hcq17 hcq20; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
      · exact Or.inr (by clear * - h hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq5 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
      · exact Or.inr (by clear * - h hcq8 hcq10 hcq17 hcq20; omega)
      · exact Or.inr (by clear * - h hcq5 hcq10 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
      · exact Or.inr (by clear * - h hcq10 hcq20; omega)
      · exact Or.inr (by clear * - h hcq10 hcq17 hcq20; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq17; omega) (by clear * - hcq0 hcq5 hcq17; omega) (by clear * - hcq17; omega) (by clear * - hcq1; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq10 hcq17; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq5 hcq17; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq10 hcq17; omega)) (Or.inr (by clear * - hcq0 hcq17; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·CG·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG78810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG78810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq8 hcq11 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7 hcq9 hcq12; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7 hcq9 hcq12; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq12; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq12; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·CG·DD` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG79810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG79810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq5 hcq13 hcq14 hcq17 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq3 hcq20; omega) (by clear * - hcq0 hcq3 hcq6 hcq20; omega) (by clear * - hcq0 hcq3 hcq20; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq20; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq20; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq20; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
