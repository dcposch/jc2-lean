import Grok810ScaleZeroQuarticChamberDefs4Scratch
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
/-- Chamber `BCDEFG` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEFG95810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG95810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hcq8 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq8 hcq17 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq8 hcq17 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq8 hcq17 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq8 hcq17 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq8 hcq17 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq5 hcq8 hcq17 hcq20; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq17; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq8 hcq17 hcq20; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8 hcq17; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq8 hcq17; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq17; omega) (by clear * - hcq0 hcq1 hcq8 hcq17; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq1 hcq8 hcq17; omega) (by clear * - hcq0 hcq5 hcq8 hcq17; omega) (by clear * - hcq0 hcq20; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq5 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq8 hcq17 hcq20; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq8 hcq17; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hcq17; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hcq17; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hcq17; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEFG97810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG97810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hcq6 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq17; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq11 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7 hcq11 hcq17 hcq20; omega)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq3 hcq17; omega) (by clear * - hcq0 hcq1 hcq3 hcq17; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq17; omega) (by clear * - hcq0 hcq1 hcq7 hcq17; omega) (by clear * - hcq0 hcq20; omega) (by clear * - hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq7; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hApos hcq17; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEFG98810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG98810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq8 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq17; omega)
      · exact Or.inr (by clear * - h hcq20; omega)
      · exact Or.inr (by clear * - h hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq20; omega)
      · exact Or.inr (by clear * - h hcq11 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq9 hcq11 hcq17 hcq20; omega)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq17; omega) (by clear * - hcq0 hcq1 hcq9 hcq17; omega) (by clear * - hcq0 hcq6 hcq17; omega) (by clear * - hcq1 hcq6 hcq17; omega) (by clear * - hcq17; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq1 hcq11 hcq17; omega) (by clear * - hcq17; omega) (by clear * - hcq0 hcq6 hcq9 hcq17; omega) (by clear * - hcq0 hcq9 hcq20; omega) (by clear * - hcq0 hcq6 hcq20; omega) (by clear * - hcq0 hcq9 hcq11; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq9 hApos hcq17; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq9 hApos hcq17; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq9 hApos hcq17; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG99810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG99810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq1 hcq5 hcq7 hcq12 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq9 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq12 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq3 hcq9 hcq12 hcq20; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq12 hcq20; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3 hcq9 hcq12 hcq20; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq12 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq12 hcq20; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq20; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq20; omega) (by clear * - hcq1 hcq12 hcq20; omega) (by clear * - hcq0; omega) (by clear * - hcq3; omega) (by clear * - hcq1 hcq9 hcq20; omega) (by clear * - hcq1 hcq3 hcq12 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq2 hcq3 hcq12; omega) (by clear * - hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq3 hcq12 hcq20; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq9 hcq12 hcq20; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq12 hcq20; omega)) (Or.inr (by clear * - hcq1 hcq12 hcq20; omega)) (Or.inr (by clear * - hcq1 hcq12 hcq20; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEFG101810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG101810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq2 hcq3 hcq4 hcq5 hcq6 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq2 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq6 hcq20; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq20; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq20; omega)
      · exact Or.inr (by clear * - h hcq2 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6 hcq20; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq6 hcq20; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ C.natDegree + F.natDegree < 2 * G.natDegree ∧ D.natDegree + E.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq20; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq20; omega)
      · exact Or.inr (by clear * - h hcq2 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5 hcq6 hcq20; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq5 hcq6 hcq20; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq2 hcq20; omega) (by clear * - hcq2 hcq6 hcq20; omega) (by clear * - hcq2 hcq20; omega) (by clear * - hcq0 hcq2 hcq6 hcq20; omega) (by clear * - hcq2 hcq20; omega) (by clear * - hcq1 hcq20; omega) (by clear * - hcq2 hcq4 hcq20; omega) (by clear * - hcq0 hcq20; omega) (by clear * - hcq0 hcq2 hcq5 hcq6 hcq20; omega) (by clear * - hcq0 hcq2 hcq4 hcq6 hcq20; omega) (by clear * - hcq2 hcq6 hcq20; omega) (by clear * - hcq2 hcq6 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq3; omega) (by clear * - hcq2 hcq6 hcq20; omega) (by clear * - hcq0 hcq2 hcq4 hcq5 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq5 hcq20; omega) (by clear * - hcq0 hcq4 hcq20; omega) (by clear * - hcq4 hcq6 hcq20; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq5 hcq6 hcq20; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq5 hcq6 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq5 hcq6 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq6 hcq20; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hdpos hpi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG103810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG103810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq7 hcq8 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7 hcq9 hcq20; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq2 hcq7 hcq20; omega) (by clear * - hcq7 hcq20; omega) (by clear * - hcq0 hcq1 hcq7 hcq20; omega) (by clear * - hcq1 hcq2 hcq7 hcq20; omega) (by clear * - hcq1 hcq2 hcq7 hcq20; omega) (by clear * - hcq0 hcq1 hcq2 hcq9; omega) (by clear * - hcq1 hcq2 hcq7 hcq20; omega) (by clear * - hcq1 hcq7 hcq9 hcq20; omega) (by clear * - hcq2 hcq7 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq0 hcq1 hcq2 hcq20; omega) (by clear * - hcq1 hcq2 hcq9; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq9 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·DD·DG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDEFG106810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG106810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq4 hcq5 hcq6 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq7 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7 hcq20; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7 hcq10 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hApos hcq10 hcq20; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq4 hcq20; omega) (by clear * - hcq1 hcq4 hcq20; omega) (by clear * - hcq4 hcq20; omega) (by clear * - hcq0 hcq1 hcq4 hcq20; omega) (by clear * - hcq4 hcq20; omega) (by clear * - hcq1 hcq4 hcq7 hcq20; omega) (by clear * - hcq0 hcq1 hcq4 hcq10 hcq20; omega) (by clear * - hcq0 hcq20; omega) (by clear * - hcq0 hcq1 hcq4 hcq7 hcq20; omega) (by clear * - hcq4 hcq10 hcq20; omega) (by clear * - hcq1 hcq4 hcq20; omega) (by clear * - hcq1 hcq4 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq1 hcq4 hcq20; omega) (by clear * - hcq1 hcq4 hcq7 hcq10 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq7 hcq20; omega) (by clear * - hcq0 hcq1 hcq10 hcq20; omega) (by clear * - hcq0 hcq10 hcq20; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos hcq10 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos hcq10 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos hcq10 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos hcq10 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos hcq10 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hdpos hpi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG107810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG107810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq2 hcq6 hcq9 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq9 hcq20; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq9 hcq20; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq9 hcq20; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq9 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq9 hcq20; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq9 hcq20; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq2 hcq9 hcq20; omega) (by clear * - hcq2 hcq20; omega) (by clear * - hcq0 hcq2 hcq4 hcq20; omega) (by clear * - hcq0 hcq2 hcq4 hcq9 hcq20; omega) (by clear * - hcq0 hcq2 hcq9 hcq20; omega) (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq0 hcq2 hcq9 hcq20; omega) (by clear * - hcq0 hcq1 hcq9 hcq20; omega) (by clear * - hcq0 hcq2 hcq4 hcq9 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq0 hcq4 hcq9 hcq20; omega) (by clear * - hcq0 hcq3 hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9 hcq20; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq9 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9 hcq20; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG109810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG109810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq4 hcq5 hcq6 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq6 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hApos hcq20; omega)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq4 hcq20; omega) (by clear * - hcq4 hcq20; omega) (by clear * - hcq0 hcq4 hcq6 hcq20; omega) (by clear * - hcq0 hcq1 hcq4 hcq6 hcq20; omega) (by clear * - hcq0 hcq1 hcq4 hcq20; omega) (by clear * - hcq0 hcq5 hcq6; omega) (by clear * - hcq0 hcq1 hcq4 hcq20; omega) (by clear * - hcq0 hcq1 hcq3 hcq20; omega) (by clear * - hcq0 hcq1 hcq4 hcq6 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq0 hcq1 hcq6 hcq20; omega) (by clear * - hcq0 hcq1 hcq5; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hcq6 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hdpos hxi; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG110810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG110810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq8 hcq13 hcq14 hcq17 hcq20 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq10 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq20; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq4 hcq20; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq10 hcq20; omega)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq2 hcq20; omega) (by clear * - hcq0 hcq2 hcq20; omega) (by clear * - hcq1; omega) (by clear * - hcq4; omega) (by clear * - hcq2 hcq10 hcq20; omega) (by clear * - hcq0 hcq2 hcq4 hcq20; omega) (by clear * - hcq20; omega) (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq0 hcq10; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos hcq10 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hApos hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos hcq10 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq20; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEFG111810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG111810 A B C D E F G)
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
    exact hnc (by clear * - hAD hcq0 hcq3 hcq4 hcq5 hcq13 hcq15 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq13 hcq15; omega)
      · exact Or.inr (by clear * - h hAD hcq14 hcq20; omega)
      · exact Or.inr (by clear * - h hAB hAD; omega)
      · exact Or.inr (by clear * - h hAB hAD hcq4; omega)
      · exact Or.inr (by clear * - h hAB hAD hcq5; omega)
      · exact Or.inr (by clear * - h hAB hAD hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAB hAD hcq4 hcq5 hcq6 hcq15 hcq18 hcq20; omega)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq14 hcq20; omega)
      · exact Or.inr (by clear * - h hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAB hcq4; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
      · exact Or.inr (by clear * - h hAB hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hcq5 hApos hcq13 hcq18 hcq20; omega)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq14 hcq20; omega)
      · exact Or.inr (by clear * - h hApos hcq13; omega)
      · exact Or.inr (by clear * - h hcq4 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAB hcq5; omega)
      · exact Or.inr (by clear * - h hcq1 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos hcq14 hcq20; omega)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq14; omega) (by clear * - hcq15; omega) (by clear * - hcq0; omega) (by clear * - hcq4 hcq15; omega) (by clear * - hcq18; omega) (by clear * - hcq20; omega) (by clear * - hcq3; omega) (by clear * - hcq5; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq3 hApos hcq13 hcq14 hcq20; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq4 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos hcq14; omega)) (Or.inr (by clear * - hApos hcq13; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hdpos hmu; omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEFG116810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG116810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hcq0 hcq1 hcq9 hApos hcq13 hcq15 hcq21 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq5 hcq7 hcq10; omega)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5 hcq7; omega) (by clear * - hAD hcq1 hcq5 hcq7; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq10; omega) (by clear * - hAD hcq1 hcq5 hcq7; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq7; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq7; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5 hcq7; omega) (by clear * - hAD hcq1 hcq7; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq10; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq7 hcq10; omega) (by clear * - hAD hcq1 hcq7; omega) (by clear * - hAD hcq0 hcq1 hcq7; omega) (by clear * - hAD hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq10; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq7 hApos hcq10; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hdpos hpi; omega

end QuarticChamberKills810

end Max11DegreeRoutes
