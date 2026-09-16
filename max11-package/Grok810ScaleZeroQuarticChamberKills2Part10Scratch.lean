import Grok810ScaleZeroQuarticChamberDefs2Scratch
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
private theorem astra4v_quarticChamberBDEF2810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hcq4 : 2 * E < A + B + F)
    (hcq6 : F < 2 * A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + B + F ∧ 3 * A + D < A + B + F ∧ A + 3 * B < A + B + F ∧ 2 * A + F < A + B + F ∧ A + B + E < A + B + F ∧ 2 * B + D < A + B + F ∧ D + E < A + B + F) := by
  have hbls : q ∨ (4 * A + B < A + B + F) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq3 hcq4 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF2810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hcq4 : 2 * E < A + B + F)
    (hcq6 : F < 2 * A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + B + F ∧ 2 * A + D < A + B + F ∧ 3 * B < A + B + F ∧ A + F < A + B + F ∧ B + E < A + B + F) := by
  have hbbetas : q ∨ (3 * A + B < A + B + F) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hCn hGn hcq0 hcq3 hcq4 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF2810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq3 : D < A + B)
    (hcq4 : 2 * E < A + B + F)
    (hcq6 : F < 2 * A + B)
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
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq3 hcq4 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEF2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq1 hcq3 hcq4 hcq6 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDEF2810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq3 hcq4 hcq6 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDEF2810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hCn hGn hcq0 hcq3 hcq4 hcq6 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBDEF2810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq3 hcq4 hcq6 hkbdelta
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq0 hcq6; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq4 hcq6; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
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
private theorem astra4v_quarticChamberBDEF4810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D + 2 * E < A + 2 * B + 2 * F)
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
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B ∧ A + B + D < A + 3 * B ∧ B + F < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF4810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D + 2 * E < A + 2 * B + 2 * F)
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
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B ∧ B + D < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF4810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D + 2 * E < A + 2 * B + 2 * F)
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
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B ∧ E < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF4810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D + 2 * E < A + 2 * B + 2 * F)
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
  · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF4810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D + 2 * E < A + 2 * B + 2 * F)
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
  · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·DD·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEF4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF4810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq3 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF4810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq3 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF4810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq3 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF4810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq3 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF4810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq3 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq3; omega) (by clear * - hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq3; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) hztheta
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
private theorem astra4v_quarticChamberBDEF6810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq3 : D < A + B)
    (hcq6 : A + 4 * B < 2 * F)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < D + E ∧ 2 * A + 2 * B < D + E ∧ 2 * A + E < D + E ∧ A + B + D < D + E ∧ B + F < D + E ∧ 2 * D < D + E) := by
  have hbls : q ∨ (5 * A < D + E) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq1 hcq3 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF6810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq3 : D < A + B)
    (hcq6 : A + 4 * B < 2 * F)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < D + E ∧ A + 2 * B < D + E ∧ A + E < D + E ∧ B + D < D + E) := by
  have hbbetas : q ∨ (4 * A < D + E) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq1 hcq3 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF6810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq3 : D < A + B)
    (hcq6 : A + 4 * B < 2 * F)
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
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq3 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF6810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : B + F = 2 * D)
    (hcq1 : A + 2 * B + 2 * F = 2 * D + 2 * E)
    (hcq3 : D < A + B)
    (hcq6 : A + 4 * B < 2 * F)
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
  · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq3 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEF6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF6810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq3 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF6810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq3 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF6810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq3 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF6810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq3 hcq6 hnbzeta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq1 hcq6; omega) (by clear * - hcq1 hcq3 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq3 hcq6; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq1 hcq6; omega))
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
private theorem astra4v_quarticChamberBDEF10810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D < B + F)
    (hcq4 : D < A + B)
    (hcq5 : 2 * E < 3 * A + 2 * B)
    (hcq8 : B + E < A + F)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B ∧ A + B + D < A + 3 * B ∧ B + F < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF10810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D < B + F)
    (hcq4 : D < A + B)
    (hcq5 : 2 * E < 3 * A + 2 * B)
    (hcq8 : B + E < A + F)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B ∧ B + D < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF10810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D < B + F)
    (hcq4 : D < A + B)
    (hcq5 : 2 * E < 3 * A + 2 * B)
    (hcq8 : B + E < A + F)
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
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B ∧ E < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF10810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D < B + F)
    (hcq4 : D < A + B)
    (hcq5 : 2 * E < 3 * A + 2 * B)
    (hcq8 : B + E < A + F)
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
  · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF10810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * D < B + F)
    (hcq8 : B + E < A + F)
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
  · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·EE·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEF10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hApos hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF10810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF10810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF10810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF10810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq8 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEF10810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq8 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq0 hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) hztheta
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
private theorem astra4v_quarticChamberBDEF14810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq2 : 2 * E < A + 2 * D)
    (hcq3 : F < A + D)
    (hcq7 : 4 * B < A + 2 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + 2 * D ∧ 3 * A + D < A + 2 * D ∧ A + 3 * B < A + 2 * D ∧ 2 * A + F < A + 2 * D ∧ A + B + E < A + 2 * D ∧ 2 * B + D < A + 2 * D ∧ D + E < A + 2 * D) := by
  have hbls : q ∨ (4 * A + B < A + 2 * D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq2 hcq3 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF14810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq2 : 2 * E < A + 2 * D)
    (hcq3 : F < A + D)
    (hcq7 : 4 * B < A + 2 * D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + 2 * D ∧ 2 * A + D < A + 2 * D ∧ 3 * B < A + 2 * D ∧ A + F < A + 2 * D ∧ B + E < A + 2 * D) := by
  have hbbetas : q ∨ (3 * A + B < A + 2 * D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq2 hcq3 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF14810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq2 : 2 * E < A + 2 * D)
    (hcq3 : F < A + D)
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
    q ∨ (2 * A + B < A + 2 * D ∧ A + D < A + 2 * D ∧ F < A + 2 * D) := by
  have hbdeltas : q ∨ (2 * A + B < A + 2 * D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEF14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEF14810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEF14810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEF14810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq7; omega) (by clear * - hcq1; omega) (by clear * - hcq2 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
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
private theorem astra4v_quarticChamberBDEF16810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
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
    q ∨ (5 * A < D + E ∧ 2 * A + 2 * B < D + E ∧ 2 * A + E < D + E ∧ A + B + D < D + E ∧ B + F < D + E ∧ 2 * D < D + E) := by
  have hbls : q ∨ (5 * A < D + E) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hGn hcq0 hcq3 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF16810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
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
    q ∨ (4 * A < D + E ∧ A + 2 * B < D + E ∧ A + E < D + E ∧ B + D < D + E) := by
  have hbbetas : q ∨ (4 * A < D + E) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hGn hcq0 hcq3 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF16810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
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
    · exact Or.inr (by clear * - h hAC hAD hApos hCn hGn hcq0 hcq3 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq8 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF16810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
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
  · exact Or.inr (by clear * - h hAC hAD hApos hCn hGn hcq0 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEF16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hGn hcq0 hcq2 hcq3 hcq6 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF16810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hGn hcq0 hcq3 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF16810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hGn hcq0 hcq3 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF16810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hApos hCn hGn hcq0 hcq3 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF16810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hApos hCn hGn hcq0 hcq3 hcq8 hnbzeta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq8; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6; omega))
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
private theorem astra4v_quarticChamberBDEF17810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : B + F < 2 * D)
    (hcq4 : F < A + D)
    (hcq7 : 4 * B < A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + D < A + 2 * B + E ∧ 2 * A + 3 * B < A + 2 * B + E ∧ 3 * A + F < A + 2 * B + E ∧ 2 * A + B + E < A + 2 * B + E ∧ A + 2 * B + D < A + 2 * B + E ∧ A + D + E < A + 2 * B + E ∧ 2 * B + F < A + 2 * B + E ∧ B + 2 * D < A + 2 * B + E ∧ E + F < A + 2 * B + E) := by
  have hbls : q ∨ (4 * A + D < A + 2 * B + E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq2 hcq4 hcq7 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF17810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : B + F < 2 * D)
    (hcq4 : F < A + D)
    (hcq7 : 4 * B < A + 2 * D)
    (hcq8 : 2 * B + E < A + 2 * D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + D < A + 2 * B + E ∧ A + 3 * B < A + 2 * B + E ∧ 2 * A + F < A + 2 * B + E ∧ A + B + E < A + 2 * B + E ∧ 2 * B + D < A + 2 * B + E ∧ D + E < A + 2 * B + E) := by
  have hbbetas : q ∨ (3 * A + D < A + 2 * B + E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq2 hcq4 hcq7 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF17810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq2 : 4 * D = A + 6 * B)
    (hcq3 : B + F < 2 * D)
    (hcq4 : F < A + D)
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
    q ∨ (2 * A + D < A + 2 * B + E ∧ 3 * B < A + 2 * B + E ∧ A + F < A + 2 * B + E ∧ B + E < A + 2 * B + E) := by
  have hbdeltas : q ∨ (2 * A + D < A + 2 * B + E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq2 hcq3 hcq4 hcq7 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `DD·DE·EE·BBB` dies on the `ξ` face `A.natDegree + 2 * B.natDegree + E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEF17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF17810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq2 hcq3 hcq4 hcq7 hApos hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF17810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq2 hcq3 hcq4 hcq7 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF17810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq2 hcq3 hcq4 hcq7 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) :=
    astra4v_quarticChamberBDEF17810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq2 hcq3 hcq4 hcq7 hcq8 hkbdelta
  have hrest : (xiQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest10810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq0 hcq2 hcq3 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq8; omega))
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
private theorem astra4v_quarticChamberBDEF20810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq2 : A + 2 * D < 2 * E)
    (hcq8 : 2 * B < E)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < 2 * E ∧ 3 * A + D < 2 * E ∧ A + 3 * B < 2 * E ∧ 2 * A + F < 2 * E ∧ A + B + E < 2 * E ∧ 2 * B + D < 2 * E ∧ D + E < 2 * E) := by
  have hbls : q ∨ (4 * A + B < 2 * E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF20810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq2 : A + 2 * D < 2 * E)
    (hcq8 : 2 * B < E)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < 2 * E ∧ 2 * A + D < 2 * E ∧ 3 * B < 2 * E ∧ A + F < 2 * E ∧ B + E < 2 * E) := by
  have hbbetas : q ∨ (3 * A + B < 2 * E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEF20810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq2 : A + 2 * D < 2 * E)
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
    q ∨ (2 * A + B < 2 * E ∧ A + D < 2 * E ∧ F < 2 * E) := by
  have hbdeltas : q ∨ (2 * A + B < 2 * E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hGn hcq0 hcq1 hcq2 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEF20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq1 hcq2 hcq5 hcq7 hcq8 hApos hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEF20810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAG hCn hGn hcq0 hcq1 hcq2 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEF20810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEF20810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hGn hcq0 hcq1 hcq2 hcq8 hkbdelta
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq2; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8; omega))
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
private theorem astra4v_quarticChamberBDEG0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hcq7 : D < A + B)
    (hcq8 : 2 * E < 3 * A + 2 * B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B ∧ A + B + D < A + 3 * B ∧ A + G < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hApos hCn hFn hcq0 hcq7 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0 hcq7 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hcq7 : D < A + B)
    (hcq8 : 2 * E < 3 * A + 2 * B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B ∧ B + D < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hApos hCn hFn hcq0 hcq7 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0 hcq7 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hcq7 : D < A + B)
    (hcq8 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B ∧ E < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAC hApos hCn hFn hcq0 hcq7 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq8 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hcq7 : D < A + B)
    (hcq8 : 2 * E < 3 * A + 2 * B)
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
  · exact Or.inr (by clear * - h hAB hAC hApos hCn hFn hcq0 hcq7 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hcq4 : 4 * E < 3 * A + 6 * B)
    (hcq7 : D < A + B)
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
  · exact Or.inr (by clear * - h hAB hApos hCn hFn hcq0 hcq4 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG0810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hFn hcq0 hcq1 hcq4 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEG0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hFn hcq0 hcq7 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEG0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hFn hcq0 hcq7 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEG0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hApos hCn hFn hcq0 hcq7 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEG0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hApos hCn hFn hcq0 hcq7 hcq8 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBDEG0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hFn hcq0 hcq4 hcq7 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq7; omega) (by clear * - hcq0; omega) (by clear * - hcq2; omega) hzl hzbeta hzdelta (Or.inr (by clear * - hcq1 hApos; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBDEG1810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq2 : D < A + B)
    (hcq4 : 2 * E < 3 * A + 2 * B)
    (hcq5 : 2 * G < 5 * A + 2 * B)
    (hcq6 : A + 2 * B < G)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 2 * A + 2 * B < B + G ∧ 2 * A + E < B + G ∧ A + B + D < B + G ∧ A + G < B + G ∧ 2 * D < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAF hCn hFn hcq2 hcq4 hcq5 hcq6; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq4 hcq5 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG1810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq2 : D < A + B)
    (hcq4 : 2 * E < 3 * A + 2 * B)
    (hcq5 : 2 * G < 5 * A + 2 * B)
    (hcq6 : A + 2 * B < G)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ A + 2 * B < B + G ∧ A + E < B + G ∧ B + D < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAF hCn hFn hcq2 hcq4 hcq5 hcq6; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq2 hcq4 hcq5 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG1810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq2 : D < A + B)
    (hcq4 : 2 * E < 3 * A + 2 * B)
    (hcq5 : 2 * G < 5 * A + 2 * B)
    (hcq6 : A + 2 * B < G)
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
    q ∨ (3 * A < B + G ∧ 2 * B < B + G ∧ E < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hFn hcq2 hcq4 hcq5 hcq6; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq4 hcq5 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG1810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq2 : D < A + B)
    (hcq4 : 2 * E < 3 * A + 2 * B)
    (hcq5 : 2 * G < 5 * A + 2 * B)
    (hcq6 : A + 2 * B < G)
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
  · exact Or.inr (by clear * - h hAC hCn hFn hcq2 hcq4 hcq5 hcq6; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDEG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG1810 A B C D E F G)
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
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hFn hcq0 hcq2 hcq4 hcq5 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDEG1810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAF hCn hFn hcq2 hcq4 hcq5 hcq6 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDEG1810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAF hCn hFn hcq2 hcq4 hcq5 hcq6 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDEG1810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hFn hcq2 hcq4 hcq5 hcq6 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBDEG1810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hFn hcq2 hcq4 hcq5 hcq6 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq6; omega) (by clear * - hcq2 hcq6; omega) (by clear * - hcq1; omega) hzl hzbeta hzdelta (Or.inr (by clear * - hcq2 hcq6; omega)) hzzeta (Or.inr (by clear * - hcq5 hcq6; omega)) (Or.inr (by clear * - hcq6; omega))
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
private theorem astra4v_quarticChamberBDEG4810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : D + E < B + G)
    (hcq3 : D < A + B)
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
    · exact Or.inr (by clear * - h hAC hAF hCn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG4810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : D + E < B + G)
    (hcq3 : D < A + B)
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
    · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG4810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : 2 * B + 2 * G = A + 4 * D)
    (hcq1 : G = A + 2 * B)
    (hcq2 : D + E < B + G)
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
    q ∨ (2 * A + B < A + 2 * D ∧ A + D < A + 2 * D) := by
  have hbdeltas : q ∨ (2 * A + B < A + 2 * D) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hFn hcq0 hcq1 hcq2 hcq3; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG4810 A B C D E F G)
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
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEG4810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAF hCn hcq0 hcq1 hcq2 hcq3 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEG4810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAF hCn hcq0 hcq1 hcq2 hcq3 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDEG4810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hFn hcq0 hcq1 hcq2 hcq3 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3; omega) (by clear * - hcq0 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3; omega))
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
private theorem astra4v_quarticChamberBDEG10810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq3 : D + E < B + G)
    (hcq4 : D < A + B)
    (hcq5 : 2 * E < 3 * A + 2 * B)
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
    · exact Or.inr (by clear * - h hAC hAF hCn hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG10810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq3 : D + E < B + G)
    (hcq4 : D < A + B)
    (hcq5 : 2 * E < 3 * A + 2 * B)
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
    · exact Or.inr (by clear * - h hAF hCn hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDEG10810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hFn : F = 0)
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq3 : D + E < B + G)
    (hcq4 : D < A + B)
    (hcq5 : 2 * E < 3 * A + 2 * B)
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
    · exact Or.inr (by clear * - h hAC hCn hFn hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG10810 A B C D E F G)
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
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq2 hcq4 hcq5 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEG10810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAF hCn hcq0 hcq1 hcq3 hcq4 hcq5 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEG10810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAF hCn hcq0 hcq1 hcq3 hcq4 hcq5 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBDEG10810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hFn hcq0 hcq1 hcq3 hcq4 hcq5 hkbdelta
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
