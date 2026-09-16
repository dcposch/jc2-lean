import Grok810ScaleZeroQuarticChamberDefs4Scratch
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG41810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D + 2 * E < A + 2 * B + 2 * F)
    (hcq6 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 3 * A + C < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B ∧ A + B + D < A + 3 * B ∧ A + 2 * C < A + 3 * B ∧ 2 * B + C < A + 3 * B ∧ A + G < A + 3 * B ∧ B + F < A + 3 * B ∧ C + E < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq2 hcq5 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq6 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG41810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D + 2 * E < A + 2 * B + 2 * F)
    (hcq6 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ 2 * A + C < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B ∧ B + D < A + 3 * B ∧ 2 * C < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq2 hcq5 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq6 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG41810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D + 2 * E < A + 2 * B + 2 * F)
    (hcq6 : D < A + B)
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
    q ∨ (3 * A < A + 3 * B ∧ A + C < A + 3 * B ∧ 2 * B < A + 3 * B ∧ E < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq2 hcq5 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG41810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D + 2 * E < A + 2 * B + 2 * F)
    (hcq6 : D < A + B)
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
    q ∨ (2 * A < A + 3 * B ∧ C < A + 3 * B) := by
  have hbzetas : q ∨ (2 * A < A + 3 * B) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq2 hcq5 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG41810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D + 2 * E < A + 2 * B + 2 * F)
    (hcq6 : D < A + B)
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
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq2 hcq5 hcq6; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG41810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq2 hcq5 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG41810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq2 hcq5 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG41810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq2 hcq5 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG41810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq2 hcq5 hcq6 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG41810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq2 hcq5 hcq6 hnbtheta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG43810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq13 : A + 4 * B < 2 * F)
    (hcq3 : 2 * G < A + 2 * F)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < D + E ∧ 3 * A + C < D + E ∧ 2 * A + 2 * B < D + E ∧ 2 * A + E < D + E ∧ A + B + D < D + E ∧ A + 2 * C < D + E ∧ 2 * B + C < D + E ∧ A + G < D + E ∧ B + F < D + E ∧ C + E < D + E ∧ 2 * D < D + E) := by
  have hbls : q ∨ (5 * A < D + E) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG43810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq13 : A + 4 * B < 2 * F)
    (hcq3 : 2 * G < A + 2 * F)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < D + E ∧ 2 * A + C < D + E ∧ A + 2 * B < D + E ∧ A + E < D + E ∧ B + D < D + E ∧ 2 * C < D + E ∧ G < D + E) := by
  have hbbetas : q ∨ (4 * A < D + E) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG43810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq13 : A + 4 * B < 2 * F)
    (hcq3 : 2 * G < A + 2 * F)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
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
    q ∨ (3 * A < D + E ∧ A + C < D + E ∧ 2 * B < D + E ∧ E < D + E) := by
  have hbdeltas : q ∨ (3 * A < D + E) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG43810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq13 : A + 4 * B < 2 * F)
    (hcq3 : 2 * G < A + 2 * F)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
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
    q ∨ (2 * A < D + E ∧ C < D + E) := by
  have hbzetas : q ∨ (2 * A < D + E) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq4 hcq6 hcq13; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG43810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG43810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG43810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG43810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbzeta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG47810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq16 : B + E < A + F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < B + F)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 3 * A + C < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B ∧ A + B + D < A + 3 * B ∧ A + 2 * C < A + 3 * B ∧ 2 * B + C < A + 3 * B ∧ A + G < A + 3 * B ∧ B + F < A + 3 * B ∧ C + E < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG47810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq16 : B + E < A + F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < B + F)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ 2 * A + C < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B ∧ B + D < A + 3 * B ∧ 2 * C < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG47810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq16 : B + E < A + F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < B + F)
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
    q ∨ (3 * A < A + 3 * B ∧ A + C < A + 3 * B ∧ 2 * B < A + 3 * B ∧ E < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG47810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq16 : B + E < A + F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < B + F)
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
    q ∨ (2 * A < A + 3 * B ∧ C < A + 3 * B) := by
  have hbzetas : q ∨ (2 * A < A + 3 * B) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG47810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq14 : B + C < F)
    (hcq16 : B + E < A + F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < B + F)
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
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG47810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG47810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG47810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG47810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDEFG47810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hnbtheta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG50810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq11 : F < 2 * A + B)
    (hcq12 : 2 * G < 5 * A + 2 * B)
    (hcq13 : A + 2 * B < G)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hcq8 : E + F < A + B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 3 * A + C < B + G ∧ 2 * A + 2 * B < B + G ∧ 2 * A + E < B + G ∧ A + B + D < B + G ∧ A + 2 * C < B + G ∧ 2 * B + C < B + G ∧ A + G < B + G ∧ B + F < B + G ∧ C + E < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq6 hcq9 hcq11 hcq12 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG50810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq11 : F < 2 * A + B)
    (hcq12 : 2 * G < 5 * A + 2 * B)
    (hcq13 : A + 2 * B < G)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hcq8 : E + F < A + B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ 2 * A + C < B + G ∧ A + 2 * B < B + G ∧ A + E < B + G ∧ B + D < B + G ∧ 2 * C < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq6 hcq9 hcq12 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG50810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq11 : F < 2 * A + B)
    (hcq12 : 2 * G < 5 * A + 2 * B)
    (hcq13 : A + 2 * B < G)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hcq8 : E + F < A + B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (3 * A < B + G ∧ A + C < B + G ∧ 2 * B < B + G ∧ E < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq9 hcq12 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG50810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq11 : F < 2 * A + B)
    (hcq12 : 2 * G < 5 * A + 2 * B)
    (hcq13 : A + 2 * B < G)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hcq8 : E + F < A + B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (2 * A < B + G ∧ C < B + G) := by
  have hbzetas : q ∨ (2 * A < B + G) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq12 hcq13; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG50810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG50810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG50810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG50810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq12 hcq13 hcq2 hcq6 hcq8 hcq9 hnbzeta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG54810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq4 : D + E < B + G)
    (hcq6 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 3 * A + C < B + G ∧ 2 * A + 2 * B < B + G ∧ 2 * A + E < B + G ∧ A + B + D < B + G ∧ A + 2 * C < B + G ∧ 2 * B + C < B + G ∧ A + G < B + G ∧ B + F < B + G ∧ C + E < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG54810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq4 : D + E < B + G)
    (hcq6 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ 2 * A + C < B + G ∧ A + 2 * B < B + G ∧ A + E < B + G ∧ B + D < B + G ∧ 2 * C < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG54810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq4 : D + E < B + G)
    (hcq6 : D < A + B)
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
    q ∨ (3 * A < B + G ∧ A + C < B + G ∧ 2 * B < B + G ∧ E < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG54810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq4 : D + E < B + G)
    (hcq6 : D < A + B)
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
    q ∨ (2 * A < B + G ∧ C < B + G) := by
  have hbzetas : q ∨ (2 * A < B + G) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq4 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq13; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG54810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG54810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG54810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG54810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq4 hcq6 hnbzeta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG55810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq10 : D < A + B)
    (hcq2 : G = A + 2 * B)
    (hcq7 : C + F < B + G)
    (hcq8 : D + E < B + G)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + D < A + B + C + D ∧ 3 * A + B + C < A + B + C + D ∧ 2 * A + 3 * B < A + B + C + D ∧ 3 * A + F < A + B + C + D ∧ 2 * A + B + E < A + B + C + D ∧ 2 * A + C + D < A + B + C + D ∧ A + 2 * B + D < A + B + C + D ∧ A + B + 2 * C < A + B + C + D ∧ 3 * B + C < A + B + C + D ∧ A + C + F < A + B + C + D ∧ A + D + E < A + B + C + D ∧ 2 * B + F < A + B + C + D ∧ B + C + E < A + B + C + D ∧ B + 2 * D < A + B + C + D ∧ 2 * C + D < A + B + C + D ∧ D + G < A + B + C + D ∧ E + F < A + B + C + D) := by
  have hbls : q ∨ (4 * A + D < A + B + C + D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq2 hcq7 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG55810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq10 : D < A + B)
    (hcq2 : G = A + 2 * B)
    (hcq7 : C + F < B + G)
    (hcq8 : D + E < B + G)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + D < A + B + C + D ∧ 2 * A + B + C < A + B + C + D ∧ A + 3 * B < A + B + C + D ∧ 2 * A + F < A + B + C + D ∧ A + B + E < A + B + C + D ∧ A + C + D < A + B + C + D ∧ 2 * B + D < A + B + C + D ∧ B + 2 * C < A + B + C + D ∧ C + F < A + B + C + D ∧ D + E < A + B + C + D) := by
  have hbbetas : q ∨ (3 * A + D < A + B + C + D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq2 hcq7 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG55810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq10 : D < A + B)
    (hcq2 : G = A + 2 * B)
    (hcq7 : C + F < B + G)
    (hcq8 : D + E < B + G)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + D < A + B + C + D ∧ A + B + C < A + B + C + D ∧ 3 * B < A + B + C + D ∧ A + F < A + B + C + D ∧ B + E < A + B + C + D ∧ C + D < A + B + C + D) := by
  have hbdeltas : q ∨ (2 * A + D < A + B + C + D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq2 hcq7 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq8 hcq10; omega)

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
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDEFG55810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq2 hcq7 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDEFG55810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq2 hcq7 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDEFG55810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq2 hcq7 hcq8 hkbdelta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG60810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : A + 2 * B + 2 * G = 4 * E)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq5 : D + E < B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 3 * A + C < B + G ∧ 2 * A + 2 * B < B + G ∧ 2 * A + E < B + G ∧ A + B + D < B + G ∧ A + 2 * C < B + G ∧ 2 * B + C < B + G ∧ A + G < B + G ∧ B + F < B + G ∧ C + E < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq5 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq9 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG60810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : A + 2 * B + 2 * G = 4 * E)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq5 : D + E < B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ 2 * A + C < B + G ∧ A + 2 * B < B + G ∧ A + E < B + G ∧ B + D < B + G ∧ 2 * C < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq5 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG60810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : A + 2 * B + 2 * G = 4 * E)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq5 : D + E < B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (3 * A < B + G ∧ A + C < B + G ∧ 2 * B < B + G ∧ E < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq5 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG60810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : A + 2 * B + 2 * G = 4 * E)
    (hcq13 : A + 2 * B < G)
    (hcq3 : C + F < B + G)
    (hcq5 : D + E < B + G)
    (hcq9 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (2 * A < B + G ∧ C < B + G) := by
  have hbzetas : q ∨ (2 * A < B + G) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq3 hcq5 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq13; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG60810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq5 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG60810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq5 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG60810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq5 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDEFG60810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq13 hcq3 hcq5 hcq9 hnbzeta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG65810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq3 : C + F < B + G)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq5 : D + E < B + G)
    (hcq7 : D < A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + 2 * D ∧ 3 * A + D < A + 2 * D ∧ 2 * A + B + C < A + 2 * D ∧ A + 3 * B < A + 2 * D ∧ 2 * A + F < A + 2 * D ∧ A + B + E < A + 2 * D ∧ A + C + D < A + 2 * D ∧ 2 * B + D < A + 2 * D ∧ B + 2 * C < A + 2 * D ∧ B + G < A + 2 * D ∧ C + F < A + 2 * D ∧ D + E < A + 2 * D) := by
  have hbls : q ∨ (4 * A + B < A + 2 * D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG65810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq5 : D + E < B + G)
    (hcq7 : D < A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + 2 * D ∧ 2 * A + D < A + 2 * D ∧ A + B + C < A + 2 * D ∧ 3 * B < A + 2 * D ∧ A + F < A + 2 * D ∧ B + E < A + 2 * D ∧ C + D < A + 2 * D) := by
  have hbbetas : q ∨ (3 * A + B < A + 2 * D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG65810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq5 : D + E < B + G)
    (hcq7 : D < A + B)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < A + 2 * D ∧ A + D < A + 2 * D ∧ B + C < A + 2 * D ∧ F < A + 2 * D) := by
  have hbdeltas : q ∨ (2 * A + B < A + 2 * D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)

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
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDEFG65810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq7 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDEFG65810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDEFG65810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hkbdelta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG71810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq10 : 2 * E < 3 * A + 2 * B)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D + E < B + G)
    (hcq9 : E + F < A + B + G)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < 2 * E ∧ 3 * A + D < 2 * E ∧ 2 * A + B + C < 2 * E ∧ A + 3 * B < 2 * E ∧ 2 * A + F < 2 * E ∧ A + B + E < 2 * E ∧ A + C + D < 2 * E ∧ 2 * B + D < 2 * E ∧ B + 2 * C < 2 * E ∧ B + G < 2 * E ∧ C + F < 2 * E ∧ D + E < 2 * E) := by
  have hbls : q ∨ (4 * A + B < 2 * E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq4 hcq6 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG71810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq10 : 2 * E < 3 * A + 2 * B)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D + E < B + G)
    (hcq9 : E + F < A + B + G)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < 2 * E ∧ 2 * A + D < 2 * E ∧ A + B + C < 2 * E ∧ 3 * B < 2 * E ∧ A + F < 2 * E ∧ B + E < 2 * E ∧ C + D < 2 * E) := by
  have hbbetas : q ∨ (3 * A + B < 2 * E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq4 hcq6 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG71810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq10 : 2 * E < 3 * A + 2 * B)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D + E < B + G)
    (hcq9 : E + F < A + B + G)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < 2 * E ∧ A + D < 2 * E ∧ B + C < 2 * E ∧ F < 2 * E) := by
  have hbdeltas : q ∨ (2 * A + B < 2 * E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq4 hcq6 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq10; omega)

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
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBCDEFG71810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq4 hcq6 hcq9 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBCDEFG71810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq4 hcq6 hcq9 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBCDEFG71810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq4 hcq6 hcq9 hkbdelta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG75810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B < 2 * C)
    (hcq10 : 2 * F < 3 * A + 2 * C)
    (hcq17 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
    (hcq8 : E < A + C)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ 2 * A + E < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ C + E < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq10 hcq17 hcq2 hcq20 hcq5 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq5 hcq8 hcq10 hcq17 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG75810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B < 2 * C)
    (hcq10 : 2 * F < 3 * A + 2 * C)
    (hcq17 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
    (hcq8 : E < A + C)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ A + E < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq10 hcq17 hcq2 hcq20 hcq5 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq5 hcq8 hcq10 hcq17 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG75810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B < 2 * C)
    (hcq10 : 2 * F < 3 * A + 2 * C)
    (hcq17 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
    (hcq8 : E < A + C)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F ∧ E < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq10 hcq17 hcq2 hcq20 hcq5 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq8 hcq10 hcq17 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG75810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * B < 2 * C)
    (hcq10 : 2 * F < 3 * A + 2 * C)
    (hcq17 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : A + 4 * D < 2 * C + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
    (hcq8 : E < A + C)
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
    q ∨ (2 * A < C + F ∧ C < C + F) := by
  have hbzetas : q ∨ (2 * A < C + F) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq10 hcq17 hcq2 hcq20 hcq3 hcq5 hcq8; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq10 hcq17; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG75810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq10 hcq17 hcq2 hcq20 hcq5 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG75810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq10 hcq17 hcq2 hcq20 hcq5 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG75810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq10 hcq17 hcq2 hcq20 hcq5 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG75810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq10 hcq17 hcq2 hcq20 hcq3 hcq5 hcq8 hnbzeta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG78810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq12 : G < 2 * A + C)
    (hcq3 : B + G < C + F)
    (hcq7 : D + G < A + C + F)
    (hcq9 : E < A + C)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ 2 * A + E < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ C + E < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq3 hcq7 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7 hcq9 hcq12; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG78810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq12 : G < 2 * A + C)
    (hcq3 : B + G < C + F)
    (hcq7 : D + G < A + C + F)
    (hcq9 : E < A + C)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ A + E < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq3 hcq7 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7 hcq9 hcq12; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG78810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq12 : G < 2 * A + C)
    (hcq3 : B + G < C + F)
    (hcq7 : D + G < A + C + F)
    (hcq9 : E < A + C)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F ∧ E < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq3 hcq7 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq9 hcq12; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG78810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq12 : G < 2 * A + C)
    (hcq3 : B + G < C + F)
    (hcq4 : A + 4 * D < 2 * C + 2 * F)
    (hcq7 : D + G < A + C + F)
    (hcq8 : 4 * E < A + 2 * C + 2 * F)
    (hcq9 : E < A + C)
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
    q ∨ (2 * A < C + F ∧ C < C + F) := by
  have hbzetas : q ∨ (2 * A < C + F) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq3 hcq4 hcq7 hcq8 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG78810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq12 hcq3 hcq7 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG78810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq12 hcq3 hcq7 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG78810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq12 hcq3 hcq7 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG78810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq12 hcq3 hcq4 hcq7 hcq8 hcq9 hnbzeta
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
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG79810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq4 : D + E < C + F)
    (hcq6 : D + G < A + C + F)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ 2 * A + E < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ C + E < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG79810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq4 : D + E < C + F)
    (hcq6 : D + G < A + C + F)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ A + E < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG79810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq4 : D + E < C + F)
    (hcq6 : D + G < A + C + F)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F ∧ E < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG79810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq4 : D + E < C + F)
    (hcq6 : D + G < A + C + F)
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
    q ∨ (2 * A < C + F ∧ C < C + F) := by
  have hbzetas : q ∨ (2 * A < C + F) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq20; omega)

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
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG79810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG79810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG79810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG79810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq6 hnbzeta
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
