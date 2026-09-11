import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart1Scratch

/-! # Single-monomial chamber kills, `(8,10)` scale zero

11 face-degree lemmas and 550 chamber kills: every leaf whose
level-0 certificate is a single monomial *and* whose eight load columns
are either empty, dominated by the chamber's own ℕ conjuncts, or covered
by the κ band of `…ChamberBandsScratch`.  Which leaves those are is
decided, with exact rational Farkas certificates, by
`scripts/derive_810_quartic_chamber_killplan.py`; the rest are named in
the residual.  Untracked working note.
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

section QuarticChamberKills810

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq3 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq7; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq2 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq6 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6 hcq7; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq6 hcq7; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq1 hcq2 hcq6 hcq7; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq2 hcq7; omega) (by clear * - hcq6 hcq7; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·DD·DE·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq7; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq7; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq3 hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq7; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq7; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq7; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq4 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq7; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq3 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq7; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq7; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq7; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq7; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq5 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq4 hcq6 hcq7; omega) (by clear * - hcq0 hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq6 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq6 hcq7; omega) (by clear * - hcq0 hcq4 hcq6 hcq7; omega) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hdpos hpi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCDEG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hFn hcq0 hcq7 hcq8 hApos hcq15 hcq16 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hcq2 hcq8 hcq16; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hAC hcq1 hcq2 hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAC hcq1 hcq2 hcq8 hcq16; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hAC hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq8 hcq16; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hAC hcq1 hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq8 hApos hcq16; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq8; omega)
      · exact Or.inr (by clear * - h hcq2 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hcq8 hcq16; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hAC hcq1 hcq8; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq8 hApos; omega)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq8; omega) (by clear * - hAC hcq8; omega) (by clear * - hcq2; omega) (by clear * - hcq8 hcq16; omega) (by clear * - hAC hcq2 hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq2 hcq8 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG27810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq6 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq14; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq14; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq14; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq6 hcq14; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq5 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq14; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG29810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq3 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq14; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq14; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq14; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq14; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ D.natDegree + E.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq14; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq3 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq14; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq1 hcq2 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq2 hcq3 hcq14; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq14; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hdpos hpi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEG31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq6 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq14; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq6 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6 hcq14; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq2 hcq6 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `CG·DD·DG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEG34810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG34810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq3 hcq4 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hFz (by clear * - hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq3 hcq6 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq6 hcq14; omega) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hdpos hpi; omega

end QuarticChamberKills810

end Max11DegreeRoutes
