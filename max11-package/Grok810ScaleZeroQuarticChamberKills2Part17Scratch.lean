import Grok810ScaleZeroQuarticChamberDefs3Scratch
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
private theorem astra4v_quarticChamberBCDFG23810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq10 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 3 * A + C < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ A + B + D < A + 3 * B ∧ A + 2 * C < A + 3 * B ∧ 2 * B + C < A + 3 * B ∧ A + G < A + 3 * B ∧ B + F < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG23810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq10 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ 2 * A + C < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ B + D < A + 3 * B ∧ 2 * C < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG23810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq10 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
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
    q ∨ (3 * A < A + 3 * B ∧ A + C < A + 3 * B ∧ 2 * B < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG23810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq10 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq5 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG23810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq10 : B + C < F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq5 : D < A + B)
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
  · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq10 hcq2 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BF·DD·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDFG23810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDFG23810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDFG23810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDFG23810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq10 hcq2 hcq3 hcq5 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCDFG23810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq10 hcq2 hcq5 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq5; omega) (by clear * - hcq1 hcq10; omega) (by clear * - hcq1 hcq2; omega) (by clear * - hcq1 hcq10; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq10; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq10; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq10; omega)) hztheta
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
private theorem astra4v_quarticChamberBCDFG26810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
    (hcq7 : F < 2 * A + B)
    (hcq8 : 2 * G < 5 * A + 2 * B)
    (hcq9 : A + 2 * B < G)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 3 * A + C < B + G ∧ 2 * A + 2 * B < B + G ∧ A + B + D < B + G ∧ A + 2 * C < B + G ∧ 2 * B + C < B + G ∧ A + G < B + G ∧ B + F < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq2 hcq5 hcq7 hcq8 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq5 hcq7 hcq8 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG26810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
    (hcq7 : F < 2 * A + B)
    (hcq8 : 2 * G < 5 * A + 2 * B)
    (hcq9 : A + 2 * B < G)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ 2 * A + C < B + G ∧ A + 2 * B < B + G ∧ B + D < B + G ∧ 2 * C < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq2 hcq5 hcq7 hcq8 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq5 hcq8 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG26810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
    (hcq7 : F < 2 * A + B)
    (hcq8 : 2 * G < 5 * A + 2 * B)
    (hcq9 : A + 2 * B < G)
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
    q ∨ (3 * A < B + G ∧ A + C < B + G ∧ 2 * B < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq2 hcq5 hcq7 hcq8 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq8 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG26810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq2 : 2 * C < A + 2 * B)
    (hcq5 : D < A + B)
    (hcq7 : F < 2 * A + B)
    (hcq8 : 2 * G < 5 * A + 2 * B)
    (hcq9 : A + 2 * B < G)
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
    · exact Or.inr (by clear * - h hEn hcq2 hcq5 hcq7 hcq8 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq8 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq2 hcq3 hcq5 hcq6 hcq8 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG26810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq2 hcq5 hcq7 hcq8 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG26810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq2 hcq5 hcq7 hcq8 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG26810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq2 hcq5 hcq7 hcq8 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG26810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq2 hcq5 hcq7 hcq8 hcq9 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq9; omega) (by clear * - hcq5 hcq9; omega) (by clear * - hcq2 hcq9; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hcq9 hApos; omega)) hzdelta (Or.inr (by clear * - hcq5 hcq9; omega)) hzzeta (Or.inr (by clear * - hcq8 hcq9; omega)) (Or.inr (by clear * - hcq9; omega))
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
private theorem astra4v_quarticChamberBCDFG30810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq3 : C + F < B + G)
    (hcq5 : D < A + B)
    (hcq9 : A + 2 * B < G)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 3 * A + C < B + G ∧ 2 * A + 2 * B < B + G ∧ A + B + D < B + G ∧ A + 2 * C < B + G ∧ 2 * B + C < B + G ∧ A + G < B + G ∧ B + F < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq5 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG30810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq3 : C + F < B + G)
    (hcq5 : D < A + B)
    (hcq9 : A + 2 * B < G)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ 2 * A + C < B + G ∧ A + 2 * B < B + G ∧ B + D < B + G ∧ 2 * C < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq5 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG30810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq3 : C + F < B + G)
    (hcq5 : D < A + B)
    (hcq9 : A + 2 * B < G)
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
    q ∨ (3 * A < B + G ∧ A + C < B + G ∧ 2 * B < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq5 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG30810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq3 : C + F < B + G)
    (hcq5 : D < A + B)
    (hcq9 : A + 2 * B < G)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq5 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BG·CG·DD` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG30810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG30810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG30810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq3 hcq5 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG30810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq3 hcq5 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG30810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq3 hcq5 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBCDFG30810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq3 hcq5 hcq9 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq9; omega) (by clear * - hcq5 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq9; omega)) hzdelta (Or.inr (by clear * - hcq5 hcq9; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq9; omega))
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
private theorem astra4v_quarticChamberBCDFG31810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq2 : G = A + 2 * B)
    (hcq7 : C + F < B + G)
    (hcq9 : D < A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + D < A + B + C + D ∧ 3 * A + B + C < A + B + C + D ∧ 2 * A + 3 * B < A + B + C + D ∧ 3 * A + F < A + B + C + D ∧ 2 * A + C + D < A + B + C + D ∧ A + 2 * B + D < A + B + C + D ∧ A + B + 2 * C < A + B + C + D ∧ 3 * B + C < A + B + C + D ∧ A + C + F < A + B + C + D ∧ 2 * B + F < A + B + C + D ∧ B + 2 * D < A + B + C + D ∧ 2 * C + D < A + B + C + D ∧ D + G < A + B + C + D) := by
  have hbls : q ∨ (4 * A + D < A + B + C + D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG31810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq2 : G = A + 2 * B)
    (hcq7 : C + F < B + G)
    (hcq9 : D < A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + D < A + B + C + D ∧ 2 * A + B + C < A + B + C + D ∧ A + 3 * B < A + B + C + D ∧ 2 * A + F < A + B + C + D ∧ A + C + D < A + B + C + D ∧ 2 * B + D < A + B + C + D ∧ B + 2 * C < A + B + C + D ∧ C + F < A + B + C + D) := by
  have hbbetas : q ∨ (3 * A + D < A + B + C + D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG31810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : A + 2 * B = 2 * C)
    (hcq1 : 2 * B + 2 * G = A + 4 * D)
    (hcq2 : G = A + 2 * B)
    (hcq7 : C + F < B + G)
    (hcq9 : D < A + B)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + D < A + B + C + D ∧ A + B + C < A + B + C + D ∧ 3 * B < A + B + C + D ∧ A + F < A + B + C + D ∧ C + D < A + B + C + D) := by
  have hbdeltas : q ∨ (2 * A + D < A + B + C + D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BG·CG·DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDFG31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq6 hcq8 hcq9 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDFG31810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq2 hcq7 hcq9 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDFG31810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq2 hcq7 hcq9 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDFG31810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq2 hcq7 hcq9 hkbdelta
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq1 hcq2 hcq9; omega) (by clear * - hcq0 hcq1 hcq2 hcq9; omega) (by clear * - hcq0 hcq1 hcq2 hcq9; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq7 hcq9; omega) (by clear * - hcq9; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9; omega))
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
private theorem astra4v_quarticChamberBCDFG35810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq3 : C + F < B + G)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + 2 * D ∧ 3 * A + D < A + 2 * D ∧ 2 * A + B + C < A + 2 * D ∧ A + 3 * B < A + 2 * D ∧ 2 * A + F < A + 2 * D ∧ A + C + D < A + 2 * D ∧ 2 * B + D < A + 2 * D ∧ B + 2 * C < A + 2 * D ∧ B + G < A + 2 * D ∧ C + F < A + 2 * D) := by
  have hbls : q ∨ (4 * A + B < A + 2 * D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG35810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + 2 * D ∧ 2 * A + D < A + 2 * D ∧ A + B + C < A + 2 * D ∧ 3 * B < A + 2 * D ∧ A + F < A + 2 * D ∧ C + D < A + 2 * D) := by
  have hbbetas : q ∨ (3 * A + B < A + 2 * D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG35810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : A + 2 * F < 2 * G)
    (hcq4 : 2 * C < A + 2 * B)
    (hcq6 : D < A + B)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq4 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BG·DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDFG35810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG35810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDFG35810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq2 hcq3 hcq4 hcq6 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDFG35810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq2 hcq4 hcq6 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDFG35810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq2 hcq4 hcq6 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq4 hcq6; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq2 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6; omega))
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
private theorem astra4v_quarticChamberBCDFG39810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * B < 2 * C)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq4 : 2 * D < A + 2 * C)
    (hcq6 : 2 * F < 3 * A + 2 * C)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq12 hcq14 hcq2 hcq4 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq4 hcq6 hcq12 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG39810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * B < 2 * C)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq4 : 2 * D < A + 2 * C)
    (hcq6 : 2 * F < 3 * A + 2 * C)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq12 hcq14 hcq2 hcq4 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq4 hcq6 hcq12 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG39810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * B < 2 * C)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq4 : 2 * D < A + 2 * C)
    (hcq6 : 2 * F < 3 * A + 2 * C)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq12 hcq14 hcq2 hcq4 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq6 hcq12 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG39810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : A + 2 * B < 2 * C)
    (hcq10 : A + 4 * B < 2 * F)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : A + 4 * D < 2 * C + 2 * F)
    (hcq4 : 2 * D < A + 2 * C)
    (hcq6 : 2 * F < 3 * A + 2 * C)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq10 hcq12 hcq14 hcq2 hcq3 hcq4 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq6 hcq12; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `CF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG39810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG39810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq2 hcq3 hcq4 hcq6 hcq9 hcq10 hcq12 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG39810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq12 hcq14 hcq2 hcq4 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG39810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq12 hcq14 hcq2 hcq4 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG39810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq12 hcq14 hcq2 hcq4 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG39810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq10 hcq12 hcq14 hcq2 hcq3 hcq4 hcq6 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq4 hcq12; omega) (by clear * - hcq12; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq6 hcq12; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq4 hcq12; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq6 hcq12; omega)) (Or.inr (by clear * - hcq0 hcq12; omega))
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
private theorem astra4v_quarticChamberBCDFG42810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : B + G < C + F)
    (hcq6 : D + G < A + C + F)
    (hcq7 : 2 * F < 3 * A + 2 * C)
    (hcq8 : G < 2 * A + C)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG42810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : B + G < C + F)
    (hcq6 : D + G < A + C + F)
    (hcq7 : 2 * F < 3 * A + 2 * C)
    (hcq8 : G < 2 * A + C)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG42810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : B + G < C + F)
    (hcq6 : D + G < A + C + F)
    (hcq7 : 2 * F < 3 * A + 2 * C)
    (hcq8 : G < 2 * A + C)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG42810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : B + G < C + F)
    (hcq4 : A + 4 * D < 2 * C + 2 * F)
    (hcq6 : D + G < A + C + F)
    (hcq7 : 2 * F < 3 * A + 2 * C)
    (hcq8 : G < 2 * A + C)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq3 hcq4 hcq6 hcq7 hcq8; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `CF·CG·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG42810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG42810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG42810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG42810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG42810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG42810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq3 hcq4 hcq6 hcq7 hcq8 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3 hcq6; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3; omega))
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
private theorem astra4v_quarticChamberBCDFG43810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + G < A + C + F)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq12 hcq14 hcq3 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG43810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + G < A + C + F)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq12 hcq14 hcq3 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG43810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + G < A + C + F)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq12 hcq14 hcq3 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG43810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq10 : A + 4 * B < 2 * F)
    (hcq12 : B + C < F)
    (hcq14 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + G < A + C + F)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq10 hcq12 hcq14 hcq3 hcq5; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `CF·CG·DD` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG43810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG43810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq4 hcq9 hcq10 hcq12 hcq14 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG43810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq12 hcq14 hcq3 hcq5 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG43810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq12 hcq14 hcq3 hcq5 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG43810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq12 hcq14 hcq3 hcq5 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG43810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq10 hcq12 hcq14 hcq3 hcq5 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq3 hcq14; omega) (by clear * - hcq0 hcq3 hcq5 hcq14; omega) (by clear * - hcq0 hcq3 hcq14; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq14; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq14; omega))
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
private theorem astra4v_quarticChamberBCDFG44810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : 2 * D < A + 2 * C)
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
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG44810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : 2 * D < A + 2 * C)
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
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG44810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : 2 * D < A + 2 * C)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG44810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : 2 * D < A + 2 * C)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `CF·CG·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG44810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG44810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG44810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG44810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG44810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG44810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq0 hcq2 hcq4 hcq6; omega) (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4; omega))
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
private theorem astra4v_quarticChamberBCDFG48810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq13 : B + C < F)
    (hcq15 : C + D < A + F)
    (hcq2 : A + 2 * B < 2 * C)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + 2 * B < C + F ∧ A + B + D < C + F ∧ A + 2 * C < C + F ∧ 2 * B + C < C + F ∧ A + G < C + F ∧ B + F < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq13 hcq15; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG48810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq13 : B + C < F)
    (hcq15 : C + D < A + F)
    (hcq2 : A + 2 * B < 2 * C)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + 2 * B < C + F ∧ B + D < C + F ∧ 2 * C < C + F ∧ G < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq13 hcq15; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG48810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq13 : B + C < F)
    (hcq15 : C + D < A + F)
    (hcq2 : A + 2 * B < 2 * C)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ 2 * B < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq15; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG48810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq13 : B + C < F)
    (hcq15 : C + D < A + F)
    (hcq2 : A + 2 * B < 2 * C)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : 2 * D < A + 2 * C)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq13 hcq15; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `CF·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG48810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG48810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG48810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG48810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG48810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDFG48810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq13 hcq15 hcq2 hcq4 hcq5 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq1 hcq13; omega) (by clear * - hcq1 hcq13 hcq15; omega) (by clear * - hcq13; omega) (by clear * - hcq1 hcq4 hcq13; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq13 hcq15; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq13 hcq15; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq13 hcq15; omega)) (Or.inr (by clear * - hcq1 hcq13; omega))
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
private theorem astra4v_quarticChamberBCDFG58810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq10 : 2 * B + C < 2 * D)
    (hcq11 : 4 * B < A + 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + 2 * D ∧ 3 * A + D < A + 2 * D ∧ 2 * A + B + C < A + 2 * D ∧ A + 3 * B < A + 2 * D ∧ 2 * A + F < A + 2 * D ∧ A + C + D < A + 2 * D ∧ 2 * B + D < A + 2 * D ∧ B + 2 * C < A + 2 * D ∧ B + G < A + 2 * D ∧ C + F < A + 2 * D) := by
  have hbls : q ∨ (4 * A + B < A + 2 * D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq10 hcq11 hcq2; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG58810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq10 : 2 * B + C < 2 * D)
    (hcq11 : 4 * B < A + 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + 2 * D ∧ 2 * A + D < A + 2 * D ∧ A + B + C < A + 2 * D ∧ 3 * B < A + 2 * D ∧ A + F < A + 2 * D ∧ C + D < A + 2 * D) := by
  have hbbetas : q ∨ (3 * A + B < A + 2 * D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq10 hcq11 hcq2; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG58810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq10 : 2 * B + C < 2 * D)
    (hcq11 : 4 * B < A + 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
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
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq10 hcq11 hcq2; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDFG58810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG58810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq2 hcq5 hcq10 hcq11 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDFG58810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq10 hcq11 hcq2 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDFG58810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq10 hcq11 hcq2 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDFG58810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq10 hcq11 hcq2 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq10; omega) (by clear * - hcq11; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq10 hcq11; omega) (by clear * - hcq0 hcq10; omega) (by clear * - hcq0 hcq2 hcq10; omega) (by clear * - hcq0 hcq1 hcq11; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hApos hcq10; omega)) hzdelta (Or.inr (by clear * - hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq10; omega)) (Or.inr (by clear * - hcq0 hApos hcq10; omega))
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
private theorem astra4v_quarticChamberBCDFG59810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * D = 2 * B + C)
    (hcq13 : 4 * B < A + 2 * D)
    (hcq14 : B + C < A + D)
    (hcq4 : B + F < 2 * D)
    (hcq7 : C + G < A + 2 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + D < A + B + C + D ∧ 3 * A + B + C < A + B + C + D ∧ 2 * A + 3 * B < A + B + C + D ∧ 3 * A + F < A + B + C + D ∧ 2 * A + C + D < A + B + C + D ∧ A + 2 * B + D < A + B + C + D ∧ A + B + 2 * C < A + B + C + D ∧ 3 * B + C < A + B + C + D ∧ A + C + F < A + B + C + D ∧ 2 * B + F < A + B + C + D ∧ B + 2 * D < A + B + C + D ∧ 2 * C + D < A + B + C + D ∧ D + G < A + B + C + D) := by
  have hbls : q ∨ (4 * A + D < A + B + C + D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq13 hcq14 hcq4 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG59810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * D = 2 * B + C)
    (hcq13 : 4 * B < A + 2 * D)
    (hcq14 : B + C < A + D)
    (hcq4 : B + F < 2 * D)
    (hcq7 : C + G < A + 2 * D)
    (hcq8 : F < A + D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + D < A + B + C + D ∧ 2 * A + B + C < A + B + C + D ∧ A + 3 * B < A + B + C + D ∧ 2 * A + F < A + B + C + D ∧ A + C + D < A + B + C + D ∧ 2 * B + D < A + B + C + D ∧ B + 2 * C < A + B + C + D ∧ C + F < A + B + C + D) := by
  have hbbetas : q ∨ (3 * A + D < A + B + C + D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq13 hcq14 hcq4 hcq7 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDFG59810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * D = 2 * B + C)
    (hcq13 : 4 * B < A + 2 * D)
    (hcq14 : B + C < A + D)
    (hcq4 : B + F < 2 * D)
    (hcq7 : C + G < A + 2 * D)
    (hcq8 : F < A + D)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + D < A + B + C + D ∧ A + B + C < A + B + C + D ∧ 3 * B < A + B + C + D ∧ A + F < A + B + C + D ∧ C + D < A + B + C + D) := by
  have hbdeltas : q ∨ (2 * A + D < A + B + C + D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq13 hcq14 hcq4 hcq7 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq14; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDFG59810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG59810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq4 hcq5 hcq8 hcq13 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDFG59810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hEn hcq0 hcq1 hcq13 hcq14 hcq4 hcq7 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDFG59810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq13 hcq14 hcq4 hcq7 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDFG59810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hEn hcq0 hcq1 hcq13 hcq14 hcq4 hcq7 hcq8 hkbdelta
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq7 hcq14; omega) (by clear * - hcq1 hcq4 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq4 hcq14; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq14; omega))
  have hlead : (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hCne hDne
  rw [degreeZeroXiQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
