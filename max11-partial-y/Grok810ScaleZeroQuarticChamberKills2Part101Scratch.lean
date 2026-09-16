import Grok810ScaleZeroQuarticChamberFacesPart101Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberDefs1Scratch
import Grok810ScaleZeroQuarticChamberRests2Scratch

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

/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace0810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hBne : B ≠ 0) :
    (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree := by
  have hc : (5 / 512 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace0810]
  rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne)]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace2810_natDegree
    (A B C D E F G : k[X])
    (hBne : B ≠ 0)
    (hGne : G ≠ 0) :
    (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace2810]
  rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace4810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace4810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace4810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0) :
    (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
  have hc : (15 / 256 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace4810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace5810_natDegree
    (A B C D E F G : k[X])
    (hBne : B ≠ 0)
    (hCne : C ≠ 0) :
    (kappaQuarticChamberFace5810 A B C D E F G).natDegree =
      B.natDegree + 2 * C.natDegree := by
  have hc : (-(15 / 128 : k)) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace5810]
  rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne)]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace3810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hFne : F ≠ 0) :
    (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace3810]
  rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace10810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0) :
    (xiQuarticChamberFace10810 A B C D E F G).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  have hc : (15 / 512 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace10810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
  simp only [natDegree_pow]
  all_goals omega

/-! ## The chamber kills unblocked by the cost ladder -/

end QuarticChamberKills2810

end Max11DegreeRoutes
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
private theorem astra4v_quarticChamberBCDEFG126810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq14 : A + 2 * B + C < 2 * E)
    (hcq16 : 2 * B < E)
    (hcq2 : A + 2 * B + 2 * G < 4 * E)
    (hcq5 : A + 2 * D < 2 * E)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq5 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG126810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq14 : A + 2 * B + C < 2 * E)
    (hcq16 : 2 * B < E)
    (hcq2 : A + 2 * B + 2 * G < 4 * E)
    (hcq5 : A + 2 * D < 2 * E)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCDEFG126810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : A + B + F < 2 * E)
    (hcq14 : A + 2 * B + C < 2 * E)
    (hcq16 : 2 * B < E)
    (hcq2 : A + 2 * B + 2 * G < 4 * E)
    (hcq5 : A + 2 * D < 2 * E)
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
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq14 hcq16 hcq2 hcq5; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14 hcq16; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG126810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG126810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq5 hcq9 hcq14 hcq15 hcq16 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBCDEFG126810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBCDEFG126810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBCDEFG126810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq1 hcq14 hcq16 hcq2 hcq5 hkbdelta
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq14; omega) (by clear * - hcq16; omega) (by clear * - hcq1; omega) (by clear * - hcq5; omega) (by clear * - hcq16; omega) (by clear * - hcq0 hcq5 hcq14 hcq16; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq16; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq14 hcq16; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq14 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq14 hcq16; omega)) (Or.inr (by clear * - hcq0 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq14 hcq16; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
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
private theorem astra4v_quarticChamberB0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAF hAG hApos hCn hDn hEn hFn; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberB0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAF hAG hApos hCn hDn hEn hFn; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberB0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
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
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAF hApos hCn hDn hEn hFn hGn; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberB0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
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
  · exact Or.inr (by clear * - h hAB hAC hAD hApos hCn hDn hEn hFn hGn; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberB0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
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
  · exact Or.inr (by clear * - h hAB hApos hCn hDn hEn hFn hGn; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `B` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberB0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberB0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFz, hGz⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hDn hEn hFn hGn hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberB0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAF hAG hApos hCn hDn hEn hFn hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberB0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAF hAG hApos hCn hDn hEn hFn hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberB0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAF hApos hCn hDn hEn hFn hGn hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberB0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hCn hDn hEn hFn hGn hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberB0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hDn hEn hFn hGn hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_B l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz hFz hGz hzl hzbeta hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBC0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : 2 * C < A + 2 * B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 3 * A + C < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ A + 2 * C < A + 3 * B ∧ 2 * B + C < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAF hAG hApos hDn hEn hFn hcq0; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBC0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : 2 * C < A + 2 * B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ 2 * A + C < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ 2 * C < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAF hAG hApos hDn hEn hFn hcq0; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBC0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C < A + 2 * B)
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
    · exact Or.inr (by clear * - h hAB hAD hAE hAF hApos hDn hEn hFn hGn hcq0; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBC0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C < A + 2 * B)
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
    · exact Or.inr (by clear * - h hAB hApos hDn hEn hFn hGn hcq0; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBC0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : 2 * C < A + 2 * B)
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
  · exact Or.inr (by clear * - h hAB hApos hDn hEn hFn hGn hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BC` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBC0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBC0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFz, hGz, hcq0, hcq1, hcq2⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hDn hEn hFn hGn hcq0 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBC0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAF hAG hApos hDn hEn hFn hcq0 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBC0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAF hAG hApos hDn hEn hFn hcq0 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBC0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAF hApos hDn hEn hFn hGn hcq0 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBC0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hDn hEn hFn hGn hcq0 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBC0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hDn hEn hFn hGn hcq0 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BC l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz hFz hGz (by clear * - hcq0; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBD0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ A + B + D < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAE hAF hApos hCn hEn hFn hGn hcq1; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBD0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ B + D < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAE hAF hApos hCn hEn hFn hGn hcq1; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBD0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : D < A + B)
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
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAC hAE hAF hApos hCn hEn hFn hGn hcq1; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBD0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : D < A + B)
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
  · exact Or.inr (by clear * - h hAB hAC hApos hCn hEn hFn hGn hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBD0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : D < A + B)
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
  · exact Or.inr (by clear * - h hAB hApos hCn hEn hFn hGn hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BD` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBD0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBD0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFz, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hEn hFn hGn hcq0 hcq1 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBD0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAE hAF hApos hCn hEn hFn hGn hcq1 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBD0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAE hAF hApos hCn hEn hFn hGn hcq1 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBD0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAE hAF hApos hCn hEn hFn hGn hcq1 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBD0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hApos hCn hEn hFn hGn hcq1 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBD0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hEn hFn hGn hcq1 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz hFz hGz (by clear * - hcq1; omega) hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hApos; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBD2810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hGn : G = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 4 * B < A + 2 * D)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + 2 * D ∧ 3 * A + D < A + 2 * D ∧ A + 3 * B < A + 2 * D ∧ 2 * B + D < A + 2 * D) := by
  have hbls : q ∨ (4 * A + B < A + 2 * D) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAE hAF hAG hCn hEn hGn hcq0 hcq1; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBD2810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hGn : G = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 4 * B < A + 2 * D)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + 2 * D ∧ 2 * A + D < A + 2 * D ∧ 3 * B < A + 2 * D) := by
  have hbbetas : q ∨ (3 * A + B < A + 2 * D) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hAF hCn hEn hGn hcq0 hcq1; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBD2810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hCn : C = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : 4 * D = A + 6 * B)
    (hcq1 : 4 * B < A + 2 * D)
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
    · exact Or.inr (by clear * - h hAC hCn hEn hFn hGn hcq0 hcq1; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BD` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBD2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBD2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFz, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hFn hGn hcq0 hcq1 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBD2810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAE hAF hAG hCn hEn hGn hcq0 hcq1 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBD2810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAE hAF hCn hEn hGn hcq0 hcq1 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) :=
    astra4v_quarticChamberBD2810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hCn hEn hFn hGn hcq0 hcq1 hkbdelta
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz hFz hGz (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
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
private theorem astra4v_quarticChamberBE0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hFn : F = 0)
    (hcq1 : 2 * E < 3 * A + 2 * B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ 2 * A + E < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAG hApos hCn hDn hFn hcq1; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBE0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hFn : F = 0)
    (hcq1 : 2 * E < 3 * A + 2 * B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ A + E < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAG hApos hCn hDn hFn hcq1; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBE0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E < 3 * A + 6 * B)
    (hcq1 : 2 * E < 3 * A + 2 * B)
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
    · exact Or.inr (by clear * - h hAB hAD hApos hCn hDn hFn hGn hcq1; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBE0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : 2 * E < 3 * A + 2 * B)
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
  · exact Or.inr (by clear * - h hAB hAC hAD hApos hCn hDn hFn hGn hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBE0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E < 3 * A + 6 * B)
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
  · exact Or.inr (by clear * - h hAB hApos hCn hDn hFn hGn hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BE` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBE0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBE0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFz, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hDn hFn hGn hcq0 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBE0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAG hApos hCn hDn hFn hcq1 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBE0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAG hApos hCn hDn hFn hcq1 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBE0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hApos hCn hDn hFn hGn hcq0 hcq1 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBE0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hCn hDn hFn hGn hcq1 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBE0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hDn hFn hGn hcq0 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hFz hGz hzl hzbeta hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBE2810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAF : 2 * F < 7 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : 2 * B < E)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < 2 * E ∧ A + 3 * B < 2 * E ∧ A + B + E < 2 * E) := by
  have hbls : q ∨ (4 * A + B < 2 * E) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hAF hAG hCn hDn hGn hcq0 hcq1; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBE2810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : 2 * B < E)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < 2 * E ∧ 3 * B < 2 * E ∧ B + E < 2 * E) := by
  have hbbetas : q ∨ (3 * A + B < 2 * E) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hAF hCn hDn hGn hcq0 hcq1; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBE2810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : 4 * E = 3 * A + 6 * B)
    (hcq1 : 2 * B < E)
    (hkbdelta : q ∨
      3 * A ≤ B + G ∨
      3 * A ≤ C + F ∨
      3 * A ≤ D + E ∨
      2 * A ≤ 3 * B ∨
      3 * A ≤ 2 * B + D ∨
      3 * A ≤ B + 2 * C ∨
      3 * A ≤ F ∨
      3 * A ≤ B + C) :
    q ∨ (2 * A + B < 2 * E) := by
  rcases hkbdelta with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAC hAD hCn hDn hFn hGn hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BE` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBE2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBE2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFz, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hFn hGn hcq1 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBE2810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hAF hAG hCn hDn hGn hcq0 hcq1 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBE2810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hAF hCn hDn hGn hcq0 hcq1 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) :=
    astra4v_quarticChamberBE2810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hFn hGn hcq0 hcq1 hkbdelta
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hFz hGz (by clear * - hcq1; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1; omega)) hzdelta (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq1; omega))
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
private theorem astra4v_quarticChamberBF0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : 4 * F < 5 * A + 6 * B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ B + F < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAG hApos hCn hDn hEn hcq0 hcq1; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBF0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAG : G < 4 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : 4 * F < 5 * A + 6 * B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAG hApos hCn hDn hEn hcq0 hcq1; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBF0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : 4 * F < 5 * A + 6 * B)
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
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hApos hCn hDn hEn hGn hcq0 hcq1; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBF0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F < A + 4 * B)
    (hcq1 : 4 * F < 5 * A + 6 * B)
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
  · exact Or.inr (by clear * - h hAB hAC hAD hApos hCn hDn hEn hGn hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBF0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F < A + 4 * B)
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
  · exact Or.inr (by clear * - h hAB hApos hCn hDn hEn hGn hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BF` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBF0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBF0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hDn hEn hGn hcq0 hcq1 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBF0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAG hApos hCn hDn hEn hcq0 hcq1 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBF0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAG hApos hCn hDn hEn hcq0 hcq1 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBF0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hApos hCn hDn hEn hGn hcq0 hcq1 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBF0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hCn hDn hEn hGn hcq0 hcq1 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBF0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hDn hEn hGn hcq0 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz hGz hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBF2810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAG : G < 4 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : F < 2 * A + B)
    (hkbl : q ∨
      5 * A ≤ B + G ∨
      5 * A ≤ C + F ∨
      5 * A ≤ D + E ∨
      4 * A ≤ 3 * B ∨
      5 * A ≤ 2 * B + D ∨
      5 * A ≤ B + 2 * C) :
    q ∨ (4 * A + B < A + B + F ∧ A + 3 * B < A + B + F ∧ 2 * A + F < A + B + F) := by
  have hbls : q ∨ (4 * A + B < A + B + F) := by
    rcases hkbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hAE hAG hCn hDn hGn hcq0 hcq1; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBF2810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : F < 2 * A + B)
    (hkbbeta : q ∨
      4 * A ≤ B + G ∨
      4 * A ≤ C + F ∨
      4 * A ≤ D + E ∨
      A ≤ B ∨
      4 * A ≤ 2 * B + D ∨
      4 * A ≤ B + 2 * C) :
    q ∨ (3 * A + B < A + B + F ∧ 3 * B < A + B + F ∧ A + F < A + B + F) := by
  have hbbetas : q ∨ (3 * A + B < A + B + F) := by
    rcases hkbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hAE hCn hDn hGn hcq0 hcq1; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBF2810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hGn : G = 0)
    (hcq0 : 2 * F = A + 4 * B)
    (hcq1 : F < 2 * A + B)
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
    · exact Or.inr (by clear * - h hAC hAD hCn hDn hEn hGn hcq0 hcq1; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BF` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBF2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBF2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hEn hGn hcq0 hcq1 hzero; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBF2810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hAE hAG hCn hDn hGn hcq0 hcq1 hkbl
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBF2810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hAE hCn hDn hGn hcq0 hcq1 hkbbeta
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) :=
    astra4v_quarticChamberBF2810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hEn hGn hcq0 hcq1 hkbdelta
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz hGz (by clear * - hcq0 hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
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
private theorem astra4v_quarticChamberBG0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ A + G < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAF hApos hCn hDn hEn hFn hcq0; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBG0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ G < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAF hApos hCn hDn hEn hFn hcq0; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBG0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hcq1 : 4 * G < 7 * A + 6 * B)
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
    q ∨ (3 * A < A + 3 * B ∧ 2 * B < A + 3 * B) := by
  have hbdeltas : q ∨ (3 * A < A + 3 * B) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hAE hAF hApos hCn hDn hEn hFn hcq0 hcq1; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBG0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
    (hcq1 : 4 * G < 7 * A + 6 * B)
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
  · exact Or.inr (by clear * - h hAB hAC hAD hApos hCn hDn hEn hFn hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBG0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : G < A + 2 * B)
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
  · exact Or.inr (by clear * - h hAB hApos hCn hDn hEn hFn hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hCn hDn hEn hFn hcq0 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBG0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAF hApos hCn hDn hEn hFn hcq0 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBG0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAF hApos hCn hDn hEn hFn hcq0 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBG0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAD hAE hAF hApos hCn hDn hEn hFn hcq0 hcq1 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBG0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hApos hCn hDn hEn hFn hcq0 hcq1 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBG0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hCn hDn hEn hFn hcq0 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz hFz (by clear * - hcq0; omega) hzl hzbeta hzdelta hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
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
private theorem astra4v_quarticChamberBG1810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : 2 * G < 5 * A + 2 * B)
    (hcq1 : A + 2 * B < G)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < B + G ∧ 2 * A + 2 * B < B + G ∧ A + G < B + G) := by
  have hbls : q ∨ (5 * A < B + G) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hAE hAF hCn hDn hEn hFn hcq0 hcq1; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBG1810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : 2 * G < 5 * A + 2 * B)
    (hcq1 : A + 2 * B < G)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < B + G ∧ A + 2 * B < B + G ∧ G < B + G) := by
  have hbbetas : q ∨ (4 * A < B + G) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hAE hAF hCn hDn hEn hFn hcq0 hcq1; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBG1810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAD : 2 * D < 5 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : 2 * G < 5 * A + 2 * B)
    (hcq1 : A + 2 * B < G)
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
    q ∨ (3 * A < B + G ∧ 2 * B < B + G) := by
  have hbdeltas : q ∨ (3 * A < B + G) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hAE hAF hCn hDn hEn hFn hcq0 hcq1; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBG1810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hCn : C = 0)
    (hDn : D = 0)
    (hEn : E = 0)
    (hFn : F = 0)
    (hcq0 : 2 * G < 5 * A + 2 * B)
    (hcq1 : A + 2 * B < G)
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
  · exact Or.inr (by clear * - h hAC hAD hCn hDn hEn hFn hcq0 hcq1; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hEn hFn hcq0 hcq1 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBG1810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hAE hAF hCn hDn hEn hFn hcq0 hcq1 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBG1810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hAE hAF hCn hDn hEn hFn hcq0 hcq1 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBG1810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAD hAE hAF hCn hDn hEn hFn hcq0 hcq1 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) :=
    astra4v_quarticChamberBG1810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hCn hDn hEn hFn hcq0 hcq1 hnbzeta
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hEz hFz (by clear * - hcq1; omega) hzl hzbeta hzdelta hzzeta (Or.inr (by clear * - hcq0 hcq1; omega)) (Or.inr (by clear * - hcq1; omega))
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
private theorem astra4v_quarticChamberDE1810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hCn : C = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < D + E ∧ 2 * A + E < D + E ∧ 2 * D < D + E) := by
  have hbls : q ∨ (5 * A < D + E) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hAF hApos hBn hCn hFn hGn hcq0; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberDE1810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hCn : C = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < D + E ∧ A + E < D + E) := by
  have hbbetas : q ∨ (4 * A < D + E) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hAD hAF hApos hBn hCn hFn hGn hcq0; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAD hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberDE1810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hCn : C = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
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
    q ∨ (3 * A < D + E ∧ E < D + E) := by
  have hbdeltas : q ∨ (3 * A < D + E) := by
    rcases hnbdelta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAC hAD hAF hApos hBn hCn hFn hGn hcq0; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq0 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberDE1810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAC : C < 2 * A)
    (hAD : 2 * D < 5 * A)
    (hApos : 0 < A)
    (hBn : B = 0)
    (hCn : C = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
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
  · exact Or.inr (by clear * - h hAC hAD hApos hBn hCn hFn hGn hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberDE1810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hApos : 0 < A)
    (hBn : B = 0)
    (hCn : C = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq0 : A + 2 * D = 2 * E)
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
  · exact Or.inr (by clear * - h hApos hBn hCn hFn hGn hcq0; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `DE` / `DD·DE·EE` dies on the `κ` face `D.natDegree + E.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberDE1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDE1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFz, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hCn hFn hGn hcq0 hApos hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberDE1810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hAF hApos hBn hCn hFn hGn hcq0 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberDE1810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hAF hApos hBn hCn hFn hGn hcq0 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberDE1810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAC hAD hAF hApos hBn hCn hFn hGn hcq0 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberDE1810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAC hAD hApos hBn hCn hFn hGn hcq0 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) :=
    astra4v_quarticChamberDE1810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hBn hCn hFn hGn hcq0 hnbtheta
  have hrest : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_DE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hFz hGz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hApos hdpos; omega)) hzzeta hztheta
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
private theorem astra4v_quarticChamberBCD0810_impossible_hzl
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : 2 * C < A + 2 * B)
    (hcq2 : D < A + B)
    (hnbl : q ∨
      6 * A ≤ D + G ∨
      6 * A ≤ E + F ∨
      5 * A ≤ 2 * B + D ∨
      6 * A ≤ 2 * B + F ∨
      6 * A ≤ B + C + E ∨
      6 * A ≤ B + 2 * D ∨
      6 * A ≤ 2 * C + D ∨
      6 * A ≤ 3 * B + C) :
    q ∨ (5 * A < A + 3 * B ∧ 3 * A + C < A + 3 * B ∧ 2 * A + 2 * B < A + 3 * B ∧ A + B + D < A + 3 * B ∧ A + 2 * C < A + 3 * B ∧ 2 * B + C < A + 3 * B ∧ 2 * D < A + 3 * B) := by
  have hbls : q ∨ (5 * A < A + 3 * B) := by
    rcases hnbl with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAF hApos hEn hFn hGn hcq1 hcq2; omega)
  rcases hbls with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1 hcq2; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCD0810_impossible_hzbeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : 2 * C < A + 2 * B)
    (hcq2 : D < A + B)
    (hnbbeta : q ∨
      5 * A ≤ D + G ∨
      5 * A ≤ E + F ∨
      4 * A ≤ 2 * B + D ∨
      5 * A ≤ 2 * B + F ∨
      5 * A ≤ B + C + E ∨
      5 * A ≤ B + 2 * D ∨
      5 * A ≤ 2 * C + D ∨
      5 * A ≤ 3 * B + C) :
    q ∨ (4 * A < A + 3 * B ∧ 2 * A + C < A + 3 * B ∧ A + 2 * B < A + 3 * B ∧ B + D < A + 3 * B ∧ 2 * C < A + 3 * B) := by
  have hbbetas : q ∨ (4 * A < A + 3 * B) := by
    rcases hnbbeta with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAF hApos hEn hFn hGn hcq1 hcq2; omega)
  rcases hbbetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hAB hcq1 hcq2; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCD0810_impossible_hzdelta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hAE : E < 3 * A)
    (hAF : 2 * F < 7 * A)
    (hApos : 0 < A)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : 2 * C < A + 2 * B)
    (hcq2 : D < A + B)
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
    · exact Or.inr (by clear * - h hAB hAE hAF hApos hEn hFn hGn hcq1 hcq2; omega)
  rcases hbdeltas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq1 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCD0810_impossible_hzzeta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : 2 * C < A + 2 * B)
    (hcq2 : D < A + B)
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
    · exact Or.inr (by clear * - h hAB hApos hEn hFn hGn hcq1 hcq2; omega)
  rcases hbzetas with h | h
  · exact Or.inl h
  · exact Or.inr (by clear * - h hcq1 hApos; omega)

set_option maxHeartbeats 64000000 in
/-- Arithmetic band conversion with abstract natural-number degrees. -/
private theorem astra4v_quarticChamberBCD0810_impossible_hztheta
    (A B C D E F G : Nat) {q : Prop}
    (hAB : 2 * B < 3 * A)
    (hApos : 0 < A)
    (hEn : E = 0)
    (hFn : F = 0)
    (hGn : G = 0)
    (hcq1 : 2 * C < A + 2 * B)
    (hcq2 : D < A + B)
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
  · exact Or.inr (by clear * - h hAB hApos hEn hFn hGn hcq1 hcq2; omega)

set_option maxHeartbeats 64000000 in
/-- Chamber `BCD` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCD0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCD0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hEn hFn hGn hcq0 hcq1 hzero; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCD0810_impossible_hzl A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAF hApos hEn hFn hGn hcq1 hcq2 hnbl
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCD0810_impossible_hzbeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAF hApos hEn hFn hGn hcq1 hcq2 hnbbeta
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCD0810_impossible_hzdelta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hAE hAF hApos hEn hFn hGn hcq1 hcq2 hnbdelta
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCD0810_impossible_hzzeta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hEn hFn hGn hcq1 hcq2 hnbzeta
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) :=
    astra4v_quarticChamberBCD0810_impossible_hztheta A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hAB hApos hEn hFn hGn hcq1 hcq2 hnbtheta
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz hGz (by clear * - hcq2; omega) (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq2; omega)) hzzeta (Or.inr (by clear * - hApos; omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hdpos hkap; omega

end QuarticChamberKills2810

end Max11DegreeRoutes
