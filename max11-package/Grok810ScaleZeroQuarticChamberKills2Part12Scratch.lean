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
private theorem astra4v_quarticChamberBDFG20810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hcq3 : F < A + D)
    (hcq8 : 4 * B < A + 2 * D)
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
    · exact Or.inr (by clear * - h hAC hAE hCn hEn hcq0 hcq2 hcq3 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG20810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hcq3 : F < A + D)
    (hcq8 : 4 * B < A + 2 * D)
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
    · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq2 hcq3 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBDFG20810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : B + F < 2 * D)
    (hcq2 : 2 * B + 2 * G < A + 4 * D)
    (hcq3 : F < A + D)
    (hcq8 : 4 * B < A + 2 * D)
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
    · exact Or.inr (by clear * - h hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG20810 A B C D E F G)
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
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq3 hcq8 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDFG20810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hCn hEn hcq0 hcq1 hcq2 hcq3 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDFG20810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBDFG20810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hcq0 hcq1 hcq2 hcq3 hcq8 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq1 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
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
private theorem astra4v_quarticChamberBEFG0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq3 : E + F < 2 * A + 3 * B)
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
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B ∧ A + G < A + 3 * B ∧ B + F < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hDn hcq0 hcq1 hcq3 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq3 : E + F < 2 * A + 3 * B)
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
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hDn hcq0 hcq1 hcq3 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq3 : E + F < 2 * A + 3 * B)
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
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hDn hcq0 hcq1 hcq3 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq8 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq2 : 4 * E < 3 * A + 6 * B)
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
  · exact Or.inr (by clear * - h hAB hAC hAD hApos hCn hDn hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : G < A + 2 * B)
    (hcq2 : 4 * E < 3 * A + 6 * B)
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
  · exact Or.inr (by clear * - h hAB hApos hCn hDn hcq0 hcq1 hcq2; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBEFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hDn hcq0 hcq1 hcq2 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hDn hcq0 hcq1 hcq3 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hDn hcq0 hcq1 hcq3 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hDn hcq0 hcq1 hcq3 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hCn hDn hcq0 hcq1 hcq2 hcq8 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hDn hcq0 hcq1 hcq2 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1; omega)) hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBEFG2810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : 2 * G < A + 2 * F)
    (hcq2 : 2 * E < A + B + F)
    (hcq3 : 2 * E < 3 * A + 2 * B)
    (hcq5 : F < 2 * A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + B + F ∧ A + 3 * B < A + B + F ∧ 2 * A + F < A + B + F ∧ A + B + E < A + B + F ∧ B + G < A + B + F) := by
  have hbls : q ∨ (4 * A + B < A + B + F) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG2810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : 2 * G < A + 2 * F)
    (hcq2 : 2 * E < A + B + F)
    (hcq3 : 2 * E < 3 * A + 2 * B)
    (hcq5 : F < 2 * A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + B + F ∧ 3 * B < A + B + F ∧ A + F < A + B + F ∧ B + E < A + B + F) := by
  have hbbetas : q ∨ (3 * A + B < A + B + F) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG2810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : 2 * G < A + 2 * F)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (2 * A + B < A + B + F ∧ F < A + B + F) := by
  have hbdeltas : q ∨ (2 * A + B < A + B + F) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBEFG2810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq5 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBEFG2810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq5 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBEFG2810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq3 hcq5 hkbdelta
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq2 hcq5; omega) (by clear * - hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
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
private theorem astra4v_quarticChamberBEFG4810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq4 : E + G < 2 * A + B + F)
    (hcq5 : F < 2 * A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + B + F ∧ A + 3 * B < A + B + F ∧ 2 * A + F < A + B + F ∧ A + B + E < A + B + F ∧ B + G < A + B + F) := by
  have hbls : q ∨ (4 * A + B < A + B + F) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq4 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG4810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq4 : E + G < 2 * A + B + F)
    (hcq5 : F < 2 * A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + B + F ∧ 3 * B < A + B + F ∧ A + F < A + B + F ∧ B + E < A + B + F) := by
  have hbbetas : q ∨ (3 * A + B < A + B + F) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hCn hDn hcq0 hcq1 hcq4 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG4810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq4 : E + G < 2 * A + B + F)
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
    q ∨ (2 * A + B < A + B + F ∧ F < A + B + F) := by
  have hbdeltas : q ∨ (2 * A + B < A + B + F) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hDn hcq0 hcq1 hcq4 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·BG·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq3 hcq5 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBEFG4810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq4 hcq5 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBEFG4810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hCn hDn hcq0 hcq1 hcq4 hcq5 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBEFG4810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hDn hcq0 hcq1 hcq4 hcq5 hkbdelta
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq1 hcq5; omega) (by clear * - hcq1 hcq2 hcq5; omega) (by clear * - hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
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
private theorem astra4v_quarticChamberBEFG5810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + B + F = 2 * E)
    (hcq2 : 2 * E < 3 * A + 2 * B)
    (hcq3 : E + G < 2 * A + B + F)
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
    q ∨ (5 * A < B + G ∧ 2 * A + 2 * B < B + G ∧ 2 * A + E < B + G ∧ A + G < B + G ∧ B + F < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG5810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + B + F = 2 * E)
    (hcq2 : 2 * E < 3 * A + 2 * B)
    (hcq3 : E + G < 2 * A + B + F)
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
    q ∨ (4 * A < B + G ∧ A + 2 * B < B + G ∧ A + E < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG5810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + B + F = 2 * E)
    (hcq2 : 2 * E < 3 * A + 2 * B)
    (hcq3 : E + G < 2 * A + B + F)
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
    q ∨ (3 * A < B + G ∧ 2 * B < B + G ∧ E < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG5810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * F = 2 * G)
    (hcq1 : A + B + F = 2 * E)
    (hcq2 : 2 * E < 3 * A + 2 * B)
    (hcq3 : E + G < 2 * A + B + F)
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
  · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·BG·EE` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBEFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG5810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG5810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG5810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG5810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq0 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq7; omega))
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
private theorem astra4v_quarticChamberBEFG10810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B ∧ A + G < A + 3 * B ∧ B + F < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG10810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG10810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
    · exact Or.inr (by clear * - h hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG10810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
  · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG10810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + B + F = 2 * E)
    (hcq1 : 2 * F = A + 4 * B)
    (hcq2 : 2 * G < A + 2 * F)
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
  · exact Or.inr (by clear * - h hAC hCn hDn hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·EE·BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBEFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG10810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG10810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG10810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG10810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBEFG10810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hDn hcq0 hcq1 hcq2 hcq8 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) hztheta
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
private theorem astra4v_quarticChamberBEFG13810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq2 : E + F < A + B + G)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (5 * A < B + G ∧ 2 * A + 2 * B < B + G ∧ 2 * A + E < B + G ∧ A + G < B + G ∧ B + F < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq5 hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG13810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq2 : E + F < A + B + G)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (4 * A < B + G ∧ A + 2 * B < B + G ∧ A + E < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG13810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq2 : E + F < A + B + G)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
    q ∨ (3 * A < B + G ∧ 2 * B < B + G ∧ E < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq3 hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG13810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq2 : E + F < A + B + G)
    (hcq3 : 2 * E < 3 * A + 2 * B)
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
  · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBEFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq4 hcq6 hcq7 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG13810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG13810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG13810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBEFG13810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq2 hcq3 hcq5 hcq6 hcq7 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq5 hcq7; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq6 hcq7; omega)) (Or.inr (by clear * - hcq7; omega))
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
private theorem astra4v_quarticChamberBEFG16810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq3 : E + F < A + B + G)
    (hcq4 : 2 * E < 3 * A + 2 * B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < 2 * E ∧ A + 3 * B < 2 * E ∧ 2 * A + F < 2 * E ∧ A + B + E < 2 * E ∧ B + G < 2 * E) := by
  have hbls : q ∨ (4 * A + B < 2 * E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq3 hcq4; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG16810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq3 : E + F < A + B + G)
    (hcq4 : 2 * E < 3 * A + 2 * B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < 2 * E ∧ 3 * B < 2 * E ∧ A + F < 2 * E ∧ B + E < 2 * E) := by
  have hbbetas : q ∨ (3 * A + B < 2 * E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hDn hcq0 hcq1 hcq3 hcq4; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG16810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : A + 2 * B + 2 * G = 4 * E)
    (hcq1 : G = A + 2 * B)
    (hcq3 : E + F < A + B + G)
    (hcq4 : 2 * E < 3 * A + 2 * B)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < 2 * E ∧ F < 2 * E) := by
  have hbdeltas : q ∨ (2 * A + B < 2 * E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hDn hcq0 hcq1 hcq3 hcq4; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BG·EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq3 hcq4 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBEFG16810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq3 hcq4 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBEFG16810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hDn hcq0 hcq1 hcq3 hcq4 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBEFG16810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hDn hcq0 hcq1 hcq3 hcq4 hkbdelta
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
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
private theorem astra4v_quarticChamberBEFG20810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq2 : A + 2 * B + 2 * G < 4 * E)
    (hcq8 : 2 * B < E)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < 2 * E ∧ A + 3 * B < 2 * E ∧ 2 * A + F < 2 * E ∧ A + B + E < 2 * E ∧ B + G < 2 * E) := by
  have hbls : q ∨ (4 * A + B < 2 * E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG20810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq2 : A + 2 * B + 2 * G < 4 * E)
    (hcq4 : G < A + E)
    (hcq8 : 2 * B < E)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < 2 * E ∧ 3 * B < 2 * E ∧ A + F < 2 * E ∧ B + E < 2 * E) := by
  have hbbetas : q ∨ (3 * A + B < 2 * E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hDn hcq0 hcq1 hcq2 hcq4 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBEFG20810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq2 : A + 2 * B + 2 * G < 4 * E)
    (hcq4 : G < A + E)
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
    q ∨ (2 * A + B < 2 * E ∧ F < 2 * E) := by
  have hbdeltas : q ∨ (2 * A + B < 2 * E) := by
    rcases hkbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hCn hDn hcq0 hcq1 hcq2 hcq4 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBEFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq3 hcq8 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBEFG20810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hcq0 hcq1 hcq2 hcq8 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBEFG20810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hDn hcq0 hcq1 hcq2 hcq4 hcq8 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBEFG20810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hDn hcq0 hcq1 hcq2 hcq4 hcq8 hkbdelta
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8; omega))
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
private theorem astra4v_quarticChamberCDEF4810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq2 : D + E < C + F)
    (hcq3 : 2 * D < A + 2 * C)
    (hcq7 : C + D < A + F)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + E < C + F ∧ A + 2 * C < C + F ∧ C + E < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF4810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq2 : D + E < C + F)
    (hcq3 : 2 * D < A + 2 * C)
    (hcq7 : C + D < A + F)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + E < C + F ∧ 2 * C < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF4810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq2 : D + E < C + F)
    (hcq3 : 2 * D < A + 2 * C)
    (hcq7 : C + D < A + F)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ E < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF4810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq2 : D + E < C + F)
    (hcq3 : 2 * D < A + 2 * C)
    (hcq7 : C + D < A + F)
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
    · exact Or.inr (by clear * - h hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF4810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C + 2 * F = A + 4 * D)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq2 : D + E < C + F)
    (hcq3 : 2 * D < A + 2 * C)
    (hcq7 : C + D < A + F)
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
    q ∨ (A < C + F) := by
  rcases hnbtheta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·DD·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEF4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF4810 A B C D E F G)
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
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq2 hcq3 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF4810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF4810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF4810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF4810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF4810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hBn hGn hcq0 hcq1 hcq2 hcq3 hcq7 hnbtheta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2; omega)) hzdelta (Or.inr (by clear * - hcq2; omega)) hzzeta hztheta
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
private theorem astra4v_quarticChamberCDEF10810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAG : G < 4 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : D + E < C + F)
    (hcq4 : 2 * D < A + 2 * C)
    (hcq5 : E < A + C)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < C + F ∧ 3 * A + C < C + F ∧ 2 * A + E < C + F ∧ A + 2 * C < C + F ∧ C + E < C + F ∧ 2 * D < C + F) := by
  have hbls : q ∨ (5 * A < C + F) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAG hBn hGn hcq0 hcq1 hcq3 hcq4 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF10810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAG : G < 4 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : D + E < C + F)
    (hcq5 : E < A + C)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < C + F ∧ 2 * A + C < C + F ∧ A + E < C + F ∧ 2 * C < C + F) := by
  have hbbetas : q ∨ (4 * A < C + F) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAG hBn hGn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF10810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : D + E < C + F)
    (hcq5 : E < A + C)
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
    q ∨ (3 * A < C + F ∧ A + C < C + F ∧ E < C + F) := by
  have hbdeltas : q ∨ (3 * A < C + F) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hBn hGn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF10810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : D + E < C + F)
    (hcq5 : E < A + C)
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
    · exact Or.inr (by clear * - h hAB hBn hGn hcq0 hcq1 hcq3 hcq5; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF10810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * C + 2 * F = 4 * E)
    (hcq1 : A + 2 * F = 4 * C)
    (hcq3 : D + E < C + F)
    (hcq5 : E < A + C)
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
    q ∨ (A < C + F) := by
  rcases hnbtheta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hBn hGn hcq0 hcq1 hcq3 hcq5; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·EE·CCC` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEF10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF10810 A B C D E F G)
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
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq2 hcq4 hcq5 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF10810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAG hBn hGn hcq0 hcq1 hcq3 hcq4 hcq5 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF10810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAG hBn hGn hcq0 hcq1 hcq3 hcq5 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF10810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hBn hGn hcq0 hcq1 hcq3 hcq5 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF10810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hBn hGn hcq0 hcq1 hcq3 hcq5 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) :=
    astra4v_quarticChamberCDEF10810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hBn hGn hcq0 hcq1 hcq3 hcq5 hnbtheta
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5; omega)) hzzeta hztheta
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
private theorem astra4v_quarticChamberCDEF16810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
    (hcq8 : 2 * C + E < 2 * A + 2 * D)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < D + E ∧ 3 * A + C < D + E ∧ 2 * A + E < D + E ∧ A + 2 * C < D + E ∧ C + E < D + E ∧ 2 * D < D + E) := by
  have hbls : q ∨ (5 * A < D + E) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hApos hBn hGn hcq0 hcq3 hcq8; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF16810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
    (hcq8 : 2 * C + E < 2 * A + 2 * D)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < D + E ∧ 2 * A + C < D + E ∧ A + E < D + E ∧ 2 * C < D + E) := by
  have hbbetas : q ∨ (4 * A < D + E) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hApos hBn hGn hcq0 hcq3 hcq8; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF16810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
    (hcq8 : 2 * C + E < 2 * A + 2 * D)
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
    q ∨ (3 * A < D + E ∧ A + C < D + E ∧ E < D + E) := by
  have hbdeltas : q ∨ (3 * A < D + E) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAC hAD hApos hBn hGn hcq0 hcq3 hcq8; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq8 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF16810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
    (hcq6 : 3 * C < A + 2 * D)
    (hcq8 : 2 * C + E < 2 * A + 2 * D)
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
    · exact Or.inr (by clear * - h hAB hAC hAD hApos hBn hGn hcq0 hcq3 hcq6 hcq8; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq6 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberCDEF16810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hcq3 : F < A + D)
    (hcq6 : 3 * C < A + 2 * D)
    (hcq8 : 2 * C + E < 2 * A + 2 * D)
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
    q ∨ (A < D + E) := by
  rcases hnbtheta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAC hApos hBn hGn hcq0 hcq3 hcq6 hcq8; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberCDEF16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF16810 A B C D E F G)
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
    exact hnc (by clear * - hAD hBn hGn hcq0 hcq2 hcq6 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberCDEF16810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hApos hBn hGn hcq0 hcq3 hcq8 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberCDEF16810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hApos hBn hGn hcq0 hcq3 hcq8 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberCDEF16810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hBn hGn hcq0 hcq3 hcq8 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberCDEF16810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hBn hGn hcq0 hcq3 hcq6 hcq8 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberCDEF16810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hApos hBn hGn hcq0 hcq3 hcq6 hcq8 hnbtheta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2; omega)) hzdelta (Or.inr (by clear * - hcq0 hApos hdpos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
