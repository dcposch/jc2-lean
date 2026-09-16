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
private theorem astra4v_quarticChamberBCDEFG80810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : D + E < C + F)
    (hcq7 : D + G < A + C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG80810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : D + E < C + F)
    (hcq7 : D + G < A + C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG80810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : D + E < C + F)
    (hcq7 : D + G < A + C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG80810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * C + 2 * F = A + 4 * D)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq5 : D + E < C + F)
    (hcq7 : D + G < A + C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq5 hcq7; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·CG·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG80810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG80810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG80810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG80810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG80810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG80810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq0 hcq2 hcq4 hcq7; omega) (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq4; omega) (by clear * - hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq7; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4; omega))
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
private theorem astra4v_quarticChamberBCDEFG85810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq5 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq8 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG85810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq5 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq8 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG85810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq5 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG85810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq20 : 4 * C < A + 2 * F)
    (hcq3 : B + G < C + F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq5 hcq8; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq8 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·CG·EE` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG85810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG85810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq8 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG85810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq5 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG85810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq5 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG85810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq5 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG85810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq5 hcq8 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq3 hcq20; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq8 hcq20; omega) (by clear * - hcq0 hcq3 hcq20; omega) (by clear * - hcq3; omega) (by clear * - hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hcq20; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq8 hcq20; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq20; omega))
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
private theorem astra4v_quarticChamberBCDEFG86810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG86810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG86810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG86810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + 2 * C + 2 * F = 4 * E)
    (hcq2 : A + 2 * F = 4 * C)
    (hcq4 : B + G < C + F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq9; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·CG·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG86810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG86810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG86810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq6 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG86810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq6 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG86810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq6 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG86810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq2 hcq4 hcq6 hcq9 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega) (by clear * - hcq0 hcq2 hcq4; omega) (by clear * - hcq4; omega) (by clear * - hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq9; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4; omega))
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
private theorem astra4v_quarticChamberBCDEFG90810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq21 : C + D < A + F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq21 hcq4 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq5 hcq18 hcq21; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG90810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq21 : C + D < A + F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq21 hcq4 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq5 hcq18 hcq21; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG90810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq21 : C + D < A + F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq21 hcq4 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq18 hcq21; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG90810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq21 : C + D < A + F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq5 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq21 hcq4 hcq5; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq21; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG90810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG90810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG90810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq21 hcq4 hcq5 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG90810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq21 hcq4 hcq5 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG90810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq21 hcq4 hcq5 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG90810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq21 hcq4 hcq5 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq18; omega) (by clear * - hcq1 hcq18 hcq21; omega) (by clear * - hcq18; omega) (by clear * - hcq1 hcq4 hcq18; omega) (by clear * - hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq18 hcq21; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq18 hcq21; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq18 hcq21; omega)) (Or.inr (by clear * - hcq1 hcq18; omega))
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
private theorem astra4v_quarticChamberBCDEFG96810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq4 hcq6 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq18; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG96810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq4 hcq6 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hcq9 hcq18; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG96810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq4 hcq6 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq18; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG96810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq18 : B + C < F)
    (hcq4 : 2 * G < A + 2 * F)
    (hcq6 : D + E < C + F)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq18 hcq4 hcq6 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq18; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG96810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG96810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq5 hcq7 hcq9 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG96810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq4 hcq6 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG96810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq4 hcq6 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG96810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq4 hcq6 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberBCDEFG96810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq18 hcq4 hcq6 hcq9 hnbzeta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq18; omega) (by clear * - hcq0 hcq1 hcq6 hcq9 hcq18; omega) (by clear * - hcq18; omega) (by clear * - hcq1 hcq4 hcq18; omega) (by clear * - hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq9 hcq18; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq9 hcq18; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq9 hcq18; omega)) (Or.inr (by clear * - hcq1 hcq18; omega))
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
private theorem astra4v_quarticChamberBCDEFG104810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq20 : 2 * C < G)
    (hcq3 : A + B + F < C + G)
    (hcq4 : A + 2 * B < 2 * C)
    (hcq5 : A + 2 * F < 2 * G)
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
    q ∨ (5 * A < D + E ∧ 3 * A + C < D + E ∧ 2 * A + 2 * B < D + E ∧ 2 * A + E < D + E ∧ A + B + D < D + E ∧ A + 2 * C < D + E ∧ 2 * B + C < D + E ∧ A + G < D + E ∧ B + F < D + E ∧ C + E < D + E ∧ 2 * D < D + E) := by
  have hbls : q ∨ (5 * A < D + E) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq9 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG104810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq20 : 2 * C < G)
    (hcq3 : A + B + F < C + G)
    (hcq4 : A + 2 * B < 2 * C)
    (hcq5 : A + 2 * F < 2 * G)
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
    q ∨ (4 * A < D + E ∧ 2 * A + C < D + E ∧ A + 2 * B < D + E ∧ A + E < D + E ∧ B + D < D + E ∧ 2 * C < D + E ∧ G < D + E) := by
  have hbbetas : q ∨ (4 * A < D + E) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG104810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq20 : 2 * C < G)
    (hcq3 : A + B + F < C + G)
    (hcq4 : A + 2 * B < 2 * C)
    (hcq5 : A + 2 * F < 2 * G)
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
    q ∨ (3 * A < D + E ∧ A + C < D + E ∧ 2 * B < D + E ∧ E < D + E) := by
  have hbdeltas : q ∨ (3 * A < D + E) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq9 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG104810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq20 : 2 * C < G)
    (hcq3 : A + B + F < C + G)
    (hcq4 : A + 2 * B < 2 * C)
    (hcq5 : A + 2 * F < 2 * G)
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
    q ∨ (2 * A < D + E ∧ C < D + E) := by
  have hbzetas : q ∨ (2 * A < D + E) := by
    rcases hnbzeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG104810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG104810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hcq7 hcq13 hcq14 hcq17 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG104810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG104810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG104810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG104810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq20 hcq3 hcq4 hcq5 hcq9 hnbzeta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq4 hcq20; omega) (by clear * - hcq0 hcq1 hcq4 hcq9 hcq20; omega) (by clear * - hcq1 hcq4 hcq20; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq1 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9 hcq20; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9 hcq20; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq9 hcq20; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq20; omega))
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
private theorem astra4v_quarticChamberBCDEFG105810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq10 : E < A + C)
    (hcq3 : G = 2 * C)
    (hcq4 : A + B + F < C + G)
    (hcq5 : A + 2 * B < 2 * C)
    (hcq6 : A + 2 * F < 2 * G)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG105810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq10 : E < A + C)
    (hcq3 : G = 2 * C)
    (hcq4 : A + B + F < C + G)
    (hcq5 : A + 2 * B < 2 * C)
    (hcq6 : A + 2 * F < 2 * G)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG105810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq10 : E < A + C)
    (hcq3 : G = 2 * C)
    (hcq4 : A + B + F < C + G)
    (hcq5 : A + 2 * B < 2 * C)
    (hcq6 : A + 2 * F < 2 * G)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG105810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : C + G = A + 2 * D)
    (hcq1 : 2 * C + 2 * G = A + 2 * D + 2 * E)
    (hcq10 : E < A + C)
    (hcq3 : G = 2 * C)
    (hcq4 : A + B + F < C + G)
    (hcq5 : A + 2 * B < 2 * C)
    (hcq6 : A + 2 * F < 2 * G)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq10; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·DD·DE·EE·CCC` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG105810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG105810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hcq8 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG105810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG105810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG105810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG105810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq10 hcq3 hcq4 hcq5 hcq6 hnbzeta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq3 hcq5; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega) (by clear * - hcq1 hcq3 hcq5; omega) (by clear * - hcq1 hcq5; omega) (by clear * - hcq1 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hcq10; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq5; omega))
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
private theorem astra4v_quarticChamberBCDEFG112810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq14 : 2 * B + C < 2 * D)
    (hcq15 : 4 * B < A + 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hcq5 : 2 * E < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq15 hcq2 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14 hcq15; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG112810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq14 : 2 * B + C < 2 * D)
    (hcq15 : 4 * B < A + 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hcq5 : 2 * E < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq15 hcq2 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq15; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG112810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq14 : 2 * B + C < 2 * D)
    (hcq15 : 4 * B < A + 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hcq5 : 2 * E < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq15 hcq2 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq15; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG112810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG112810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq5 hcq6 hcq14 hcq15 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDEFG112810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq15 hcq2 hcq5 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDEFG112810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq15 hcq2 hcq5 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBCDEFG112810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq15 hcq2 hcq5 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq14; omega) (by clear * - hcq15; omega) (by clear * - hcq1; omega) (by clear * - hcq5 hcq15; omega) (by clear * - hcq0 hcq14 hcq15; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq0 hcq1 hcq15; omega) (by clear * - hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hApos hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq5 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq14; omega)) (Or.inr (by clear * - hcq0 hApos hcq14; omega))
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
private theorem astra4v_quarticChamberBCDEFG113810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * D = 2 * B + C)
    (hcq19 : B + C < A + D)
    (hcq4 : B + F < 2 * D)
    (hcq7 : C + G < A + 2 * D)
    (hcq8 : 2 * E < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq19 hcq4 hcq7 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7 hcq8 hcq19; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG113810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * D = 2 * B + C)
    (hcq19 : B + C < A + D)
    (hcq4 : B + F < 2 * D)
    (hcq7 : C + G < A + 2 * D)
    (hcq8 : 2 * E < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq19 hcq4 hcq7 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8 hcq19; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG113810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 2 * D = 2 * B + C)
    (hcq19 : B + C < A + D)
    (hcq4 : B + F < 2 * D)
    (hcq7 : C + G < A + 2 * D)
    (hcq8 : 2 * E < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq19 hcq4 hcq7 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq8 hcq19; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG113810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG113810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq4 hcq5 hcq8 hcq9 hcq17 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDEFG113810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq19 hcq4 hcq7 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDEFG113810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq19 hcq4 hcq7 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) :=
    astra4v_quarticChamberBCDEFG113810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq19 hcq4 hcq7 hcq8 hkbdelta
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq19; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq19; omega) (by clear * - hcq19; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq7 hcq19; omega) (by clear * - hcq1 hcq4 hcq19; omega) (by clear * - hcq0 hcq1 hcq8 hcq19; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq1 hcq19; omega) (by clear * - hcq0 hcq1 hcq7 hcq8; omega) (by clear * - hcq1 hcq4 hcq19; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hcq19; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hcq19; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq19; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8 hcq19; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq19; omega))
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
private theorem astra4v_quarticChamberBCDEFG118810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq16 : 2 * B + E < A + 2 * D)
    (hcq18 : B + C < A + D)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq6 : F < A + D)
    (hcq9 : E + G < 2 * A + 2 * D)
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
    · exact Or.inr (by clear * - h hAD hcq0 hcq16 hcq18 hcq22 hcq6 hcq9; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq6 hcq9 hcq16 hcq18 hcq22; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG118810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq16 : 2 * B + E < A + 2 * D)
    (hcq18 : B + C < A + D)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq6 : F < A + D)
    (hcq9 : E + G < 2 * A + 2 * D)
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
    · exact Or.inr (by clear * - h hAD hcq0 hcq16 hcq18 hcq22 hcq6 hcq9; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq9 hcq16 hcq22; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG118810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq16 : 2 * B + E < A + 2 * D)
    (hcq18 : B + C < A + D)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq6 : F < A + D)
    (hcq9 : E + G < 2 * A + 2 * D)
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
    · exact Or.inr (by clear * - h hAD hApos hcq0 hcq16 hcq18 hcq22 hcq6 hcq9; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hApos hcq16 hcq22; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG118810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq14 : 2 * B + C < 2 * D)
    (hcq16 : 2 * B + E < A + 2 * D)
    (hcq18 : B + C < A + D)
    (hcq20 : 3 * C < A + 2 * D)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq6 : F < A + D)
    (hcq9 : E + G < 2 * A + 2 * D)
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
    · exact Or.inr (by clear * - h hAD hApos hcq0 hcq14 hcq16 hcq18 hcq20 hcq22 hcq6 hcq9; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hApos hcq20; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG118810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG118810 A B C D E F G)
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
    exact hnc (by clear * - hAD hcq0 hcq2 hcq3 hcq6 hcq13 hcq15 hcq20 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG118810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hcq0 hcq16 hcq18 hcq22 hcq6 hcq9 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG118810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hcq0 hcq16 hcq18 hcq22 hcq6 hcq9 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG118810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hApos hcq0 hcq16 hcq18 hcq22 hcq6 hcq9 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG118810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hApos hcq0 hcq14 hcq16 hcq18 hcq20 hcq22 hcq6 hcq9 hnbzeta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq13; omega) (by clear * - hcq0 hcq16; omega) (by clear * - hcq0 hcq14 hcq20; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hApos hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq16; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq13; omega))
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
private theorem astra4v_quarticChamberBCDEFG119810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * D = 2 * E)
    (hcq14 : 2 * B + C < 2 * D)
    (hcq16 : 2 * B + E < A + 2 * D)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : B + F < 2 * D)
    (hcq4 : 2 * B + 2 * G < A + 4 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + D < A + 2 * B + E ∧ 3 * A + B + C < A + 2 * B + E ∧ 2 * A + 3 * B < A + 2 * B + E ∧ 3 * A + F < A + 2 * B + E ∧ 2 * A + B + E < A + 2 * B + E ∧ 2 * A + C + D < A + 2 * B + E ∧ A + 2 * B + D < A + 2 * B + E ∧ A + B + 2 * C < A + 2 * B + E ∧ 3 * B + C < A + 2 * B + E ∧ A + C + F < A + 2 * B + E ∧ A + D + E < A + 2 * B + E ∧ 2 * B + F < A + 2 * B + E ∧ B + C + E < A + 2 * B + E ∧ B + 2 * D < A + 2 * B + E ∧ 2 * C + D < A + 2 * B + E ∧ D + G < A + 2 * B + E ∧ E + F < A + 2 * B + E) := by
  have hbls : q ∨ (4 * A + D < A + 2 * B + E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq14 hcq16 hcq2 hcq3 hcq4; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG119810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * D = 2 * E)
    (hcq14 : 2 * B + C < 2 * D)
    (hcq16 : 2 * B + E < A + 2 * D)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : B + F < 2 * D)
    (hcq4 : 2 * B + 2 * G < A + 4 * D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + D < A + 2 * B + E ∧ 2 * A + B + C < A + 2 * B + E ∧ A + 3 * B < A + 2 * B + E ∧ 2 * A + F < A + 2 * B + E ∧ A + B + E < A + 2 * B + E ∧ A + C + D < A + 2 * B + E ∧ 2 * B + D < A + 2 * B + E ∧ B + 2 * C < A + 2 * B + E ∧ C + F < A + 2 * B + E ∧ D + E < A + 2 * B + E) := by
  have hbbetas : q ∨ (3 * A + D < A + 2 * B + E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq14 hcq16 hcq2 hcq3 hcq4; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG119810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * D = 2 * E)
    (hcq14 : 2 * B + C < 2 * D)
    (hcq16 : 2 * B + E < A + 2 * D)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : B + F < 2 * D)
    (hcq4 : 2 * B + 2 * G < A + 4 * D)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + D < A + 2 * B + E ∧ A + B + C < A + 2 * B + E ∧ 3 * B < A + 2 * B + E ∧ A + F < A + 2 * B + E ∧ B + E < A + 2 * B + E ∧ C + D < A + 2 * B + E) := by
  have hbdeltas : q ∨ (2 * A + D < A + 2 * B + E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq14 hcq16 hcq2 hcq3 hcq4; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·DE·EE·BBB` dies on the `ξ` face `A.natDegree + 2 * B.natDegree + E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG119810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG119810 A B C D E F G)
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
  have hdpos : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq2 hcq3 hcq4 hcq7 hcq14 hcq15 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG119810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq16 hcq2 hcq3 hcq4 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG119810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq16 hcq2 hcq3 hcq4 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG119810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq16 hcq2 hcq3 hcq4 hkbdelta
  have hrest : (xiQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest10810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq16; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq0 hcq2 hcq16; omega) (by clear * - hcq0 hcq2 hcq14 hcq16; omega) (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq0 hcq2 hcq4 hcq16; omega) (by clear * - hcq0 hcq2 hcq3 hcq14 hcq16; omega) (by clear * - hcq0 hcq2 hcq16; omega) (by clear * - hcq2 hcq14; omega) (by clear * - hcq0 hcq2 hcq14 hcq16; omega) (by clear * - hcq2 hcq4; omega) (by clear * - hcq0 hcq2 hcq3 hcq16; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq14 hcq16; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq14 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq14 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq14 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq14 hcq16; omega))
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
private theorem astra4v_quarticChamberBCDEFG121810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * D = 2 * E)
    (hcq15 : 2 * B + C < 2 * D)
    (hcq2 : A + 2 * D = 3 * C)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq3 : B + F < 2 * D)
    (hcq5 : 2 * C + 2 * F < A + 4 * D)
    (hcq6 : C + G < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6 hcq15 hcq22; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG121810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * D = 2 * E)
    (hcq15 : 2 * B + C < 2 * D)
    (hcq2 : A + 2 * D = 3 * C)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq3 : B + F < 2 * D)
    (hcq5 : 2 * C + 2 * F < A + 4 * D)
    (hcq6 : C + G < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hcq15 hcq22; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG121810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * D = 2 * E)
    (hcq15 : 2 * B + C < 2 * D)
    (hcq2 : A + 2 * D = 3 * C)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq3 : B + F < 2 * D)
    (hcq5 : 2 * C + 2 * F < A + 4 * D)
    (hcq6 : C + G < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq15 hcq22; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG121810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : A + 2 * D = 2 * E)
    (hcq15 : 2 * B + C < 2 * D)
    (hcq2 : A + 2 * D = 3 * C)
    (hcq22 : 2 * C + E < 2 * A + 2 * D)
    (hcq3 : B + F < 2 * D)
    (hcq5 : 2 * C + 2 * F < A + 4 * D)
    (hcq6 : C + G < A + 2 * D)
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
    · exact Or.inr (by clear * - h hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq22; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·DE·EE·CCC` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG121810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG121810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq2 hcq4 hcq5 hcq7 hcq14 hcq16 hcq21 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG121810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG121810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG121810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBCDEFG121810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq15 hcq2 hcq22 hcq3 hcq5 hcq6 hnbzeta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq2 hcq15; omega) (by clear * - hcq0 hcq2 hcq15 hcq22; omega) (by clear * - hcq0 hcq2 hcq15; omega) (by clear * - hcq0 hcq2 hcq6 hcq15; omega) (by clear * - hcq0 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq15 hcq22; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq15 hcq22; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq2 hcq15 hcq22; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq15; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
