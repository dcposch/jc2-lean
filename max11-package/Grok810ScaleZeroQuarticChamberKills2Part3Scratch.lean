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
/-- Chamber `BCD` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCD4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCD4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, hq0, hq1, hq2, hq3, hq4, hq5, hq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz hGz (by omega) (by omega) (by omega) (by omega) hzl hzbeta (Or.inr ⟨by omega, by omega, by omega⟩) hzdelta (Or.inr (by omega)) (Or.inr ⟨by omega, by omega⟩) (Or.inr (by omega)) (Or.inr (by omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCD` / `DD·BBB·BBC·BCC·CCC` dies on the `ξ` face `A.natDegree + B.natDegree + C.natDegree + D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCD5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCD5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, hq0, hq1, hq2, hq3, hq4, hq5, hq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hrest : (xiQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest4810_natDegree_lt_of_live_BCD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz hGz (by omega) (by omega) (by omega) (by omega) hzl hzbeta (Or.inr ⟨by omega, by omega, by omega⟩) hzdelta (Or.inr ⟨by omega, by omega, by omega⟩) (Or.inr ⟨by omega, by omega⟩) (Or.inr (by omega)) (Or.inr (by omega))
  have hlead : (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hCne hDne
  rw [degreeZeroXiQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCE` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCE0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCE0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, hq0, hq1, hq2, hq3, hq4, hq5, hq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hFz hGz (by omega) hzl hzbeta (Or.inr (by omega)) hzdelta hzzeta (Or.inr (by omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCE` / `EE·BBB` dies on the `μ` face `2 * E.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCE4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCE4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, hq0, hq1, hq2, hq3, hq4, hq5, hq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hFz hGz (by omega) (by omega) (by omega) (by omega) hzl hzbeta (Or.inr ⟨by omega, by omega⟩) hzdelta (Or.inr ⟨by omega, by omega⟩) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCE` / `EE·CCC` dies on the `κ` face `B.natDegree + 2 * C.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCE6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCE6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, hq0, hq1, hq2, hq3, hq4, hq5, hq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hrest : (kappaQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest5810_natDegree_lt_of_live_BCE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hFz hGz (by omega) hzl hzbeta (Or.inr (by omega)) hzdelta hzzeta (Or.inr (by omega)) (Or.inr (by omega))
  have hlead : (kappaQuarticChamberFace5810 A B C D E F G).natDegree =
      B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberFace5810_natDegree A B C D E F G hBne hCne
  rw [degreeZeroKappaQuartic810_eq_face5_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCF` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCF0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCF0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, hq0, hq1, hq2, hq3, hq4, hq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz hGz (by omega) (by omega) hzl hzbeta (Or.inr ⟨by omega, by omega⟩) hzdelta hzzeta (Or.inr (by omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCF` / `BF·BBB` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, hq0, hq1, hq2, hq3, hq4, hq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz hGz (by omega) (by omega) (by omega) hzl hzbeta (Or.inr ⟨by omega, by omega⟩) hzdelta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCF` / `CF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCF9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCF9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, hq0, hq1, hq2, hq3, hq4, hq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz hGz (by omega) (by omega) hzl hzbeta (Or.inr ⟨by omega, by omega⟩) hzdelta hzzeta (Or.inr (by omega)) (Or.inr (by omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCG` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, hq0, hq1, hq2, hq3, hq4, hq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz hFz (by omega) (by omega) hzl hzbeta (Or.inr (by omega)) hzdelta hzzeta (Or.inr (by omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BCG` / `BG` dies on the `κ` face `B.natDegree + G.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, hq0, hq1, hq2, hq3, hq4, hq5⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hrest : (kappaQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest2810_natDegree_lt_of_live_BCG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz hFz (by omega) (by omega) hzl hzbeta (Or.inr (by omega)) hzdelta hzzeta (Or.inr (by omega)) (Or.inr (by omega))
  have hlead : (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace2810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BDE` / `BBB` dies on the `κ` face `A.natDegree + 3 * B.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBDE0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDE0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + 3 * B.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hztheta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hrest : (kappaQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest0810_natDegree_lt_of_live_BDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz hGz (by omega) (by omega) hzl hzbeta hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega)) hztheta
  have hlead : (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberFace0810_natDegree A B C D E F G hAne hBne
  rw [degreeZeroKappaQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega
set_option maxHeartbeats 64000000 in
/-- Chamber `BDE` / `DD·BBB` dies on the `μ` face `A.natDegree + 2 * D.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDE2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDE2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz : A.natDegree = 0 := by simp [h0]
    omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc ⟨by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz hGz (by omega) (by omega) (by omega) hzl hzbeta (Or.inr ⟨by omega, by omega⟩) hzdelta (Or.inr ⟨by omega, by omega⟩) (Or.inr ⟨by omega, by omega⟩) (Or.inr (by omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  omega

end QuarticChamberKills2810

end Max11DegreeRoutes
