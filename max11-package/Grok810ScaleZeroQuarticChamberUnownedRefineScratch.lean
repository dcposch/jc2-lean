import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN7BandsScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedRefineRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems9Part2Scratch

/-! # Unowned refinement trees, `(8,10)` scale zero

1 chambers of `UNOWNED_CHAMBERS.md` §11 that need a nested case
split.  The pivots come from the plan; the tree itself, every leaf's
carrier and face, and every load-column verdict are re-derived here
with the exact rational Farkas engine, so no branch is emitted on the
plan's word.  Untracked working note.
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

section QuarticChamberUnownedRefine810

/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace8000810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (kappaQuarticChamberFace8000810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace8000810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberFace8000810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hGne : G ≠ 0) :
    (n2QuarticChamberFace8000810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [n2QuarticChamberFace8000810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hGne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberFace8000810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0) :
    (n3QuarticChamberFace8000810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + G.natDegree := by
  have hc : (-(15 / 256 : k)) ≠ 0 := by norm_num
  simp only [n3QuarticChamberFace8000810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace8000810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0) :
    (muQuarticChamberFace8000810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree := by
  have hc : (-(5 / 128 : k)) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace8000810]
  rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne)]
  simp only [natDegree_pow]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace8000810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0) :
    (xiQuarticChamberFace8000810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree := by
  have hc : (-(5 / 64 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace8000810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
  all_goals omega

/-! ## The refinement-tree kills -/

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DEFG` / `DD` dies on a 13-leaf refinement tree (4 nested pivots). -/
theorem quarticChamberDEFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  rcases lt_trichotomy (A.natDegree + D.natDegree + F.natDegree) (E.natDegree + G.natDegree) with hpv | hpv | hpv
  ·
    rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (2 * D.natDegree + E.natDegree) with hpv | hpv | hpv
    ·
      rcases lt_trichotomy (D.natDegree + G.natDegree) (A.natDegree) with hpv | hpv | hpv
      ·
        have hdpos : 0 < D.natDegree + E.natDegree := by
          omega
        have hdzpos : 0 < D.natDegree + E.natDegree := by omega
        obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
          quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hkap
        obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
          quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hnu hkap
        have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
          have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbl with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq0; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          rcases hbls with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
        have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
          have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbbeta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq0; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          rcases hbbetas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
        have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
          have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbdelta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq0; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          rcases hbdeltas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq0 hApos; omega)
        have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hq0; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
        have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
          rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hApos; omega)
        have hrest : (kappaQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < D.natDegree + E.natDegree :=
          kappaQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta hztheta
        have hlead : (kappaQuarticChamberFace8000810 A B C D E F G).natDegree =
            D.natDegree + E.natDegree :=
          kappaQuarticChamberFace8000810_natDegree A B C D E F G hDne hEne
        rw [degreeZeroKappaQuartic810_eq_face8000_add_rest,
          natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
          at hkap
        omega
      ·
        have hdpos : 0 < D.natDegree + E.natDegree := by
          omega
        have hdzpos : 0 < D.natDegree + E.natDegree := by omega
        obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
          quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hkap
        obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
          quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hnu hkap
        have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
          have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbl with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq0; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          rcases hbls with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
        have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
          have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbbeta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq0; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          rcases hbbetas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
        have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
          have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbdelta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq0; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          rcases hbdeltas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq0 hApos; omega)
        have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hq0; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
        have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
          rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hApos; omega)
        have hrest : (kappaQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < D.natDegree + E.natDegree :=
          kappaQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta hztheta
        have hlead : (kappaQuarticChamberFace8000810 A B C D E F G).natDegree =
            D.natDegree + E.natDegree :=
          kappaQuarticChamberFace8000810_natDegree A B C D E F G hDne hEne
        rw [degreeZeroKappaQuartic810_eq_face8000_add_rest,
          natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
          at hkap
        omega
      ·
        rcases lt_trichotomy (2 * D.natDegree + E.natDegree) (2 * G.natDegree) with hpv | hpv | hpv
        ·
          have hdpos : A.natDegree < D.natDegree + G.natDegree := by
            omega
          have hdzpos : 0 < D.natDegree + G.natDegree := by omega
          obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
            quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G hA homi hnu hkap
          obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
            quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G hA hprim homi hnu hkap
          have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * E.natDegree < D.natDegree + G.natDegree) := by
            have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
              rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1 hq2; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hq2; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAC hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
            rcases hbls with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0 hq1 hq2; omega)
          have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
            have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
              rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hq2; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
            rcases hbbetas with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
          have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
            have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
              rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAC hAD hBn hCn hq2; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
            rcases hbdeltas with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0 hq2 hApos; omega)
          have hzzeta : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree ∧ E.natDegree < D.natDegree + G.natDegree) := by
            have hbzetas : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree) := by
              rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
            rcases hbzetas with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0; omega)
          have hztheta : theta = 0 ∨ (2 * A.natDegree < D.natDegree + G.natDegree) := by
            rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hq1; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hBn hCn hq2 hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hCn hq1; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
            · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
            · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hCn hq1; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hAD hBn hApos; omega)
            · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
            · exact Or.inr (by clear * - h hAD hCn hApos; omega)
            · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hq1; omega)
            · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          have hrest : (n2QuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G).natDegree < D.natDegree + G.natDegree :=
            n2QuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
              A B C D E F G hdzpos hBz hCz (by omega) hzl hzbeta hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega)) hztheta
          have hlead : (n2QuarticChamberFace8000810 A B C D E F G).natDegree =
              D.natDegree + G.natDegree :=
            n2QuarticChamberFace8000810_natDegree A B C D E F G hDne hGne
          have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
            A B C D E F G hnu hkap
          rw [degreeZeroN2Quartic810_eq_face8000_add_rest,
            natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
            at hle
          omega
        ·
          have hdpos : 0 < D.natDegree + E.natDegree := by
            omega
          have hdzpos : 0 < D.natDegree + E.natDegree := by omega
          obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
            quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G hA hnu hkap
          obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
            quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G hA hprim homi hnu hkap
          have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
            have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
              rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hq0; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAC hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
            rcases hbls with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
          have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
            have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
              rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hq0; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
            rcases hbbetas with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
          have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
            have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
              rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAB hAC hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
            rcases hbdeltas with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hq0 hApos; omega)
          have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq1; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hBn hq1; omega)
            · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hAD hCn hApos; omega)
            · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
            · exact Or.inr (by clear * - h hAD hCn hApos; omega)
            · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hq1; omega)
            · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          have hrest : (kappaQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G).natDegree < D.natDegree + E.natDegree :=
            kappaQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
              A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega))
          have hlead : (kappaQuarticChamberFace8000810 A B C D E F G).natDegree =
              D.natDegree + E.natDegree :=
            kappaQuarticChamberFace8000810_natDegree A B C D E F G hDne hEne
          rw [degreeZeroKappaQuartic810_eq_face8000_add_rest,
            natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
            at hkap
          omega
        ·
          have hdpos : 0 < D.natDegree + E.natDegree := by
            omega
          have hdzpos : 0 < D.natDegree + E.natDegree := by omega
          obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
            quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G hA hnu hkap
          obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
            quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G hA hprim homi hnu hkap
          have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
            have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
              rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hq0; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAC hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
            rcases hbls with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
          have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
            have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
              rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq2; omega)
              · exact Or.inr (by clear * - h hAC hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hq0; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
            rcases hbbetas with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
          have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
            have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
              rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hq2; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hCn hq0; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
              · exact Or.inr (by omega)
              · exact Or.inr (by clear * - h hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hBn hCn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hBn hApos; omega)
              · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
              · exact Or.inr (by clear * - h hAD hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
              · exact Or.inr (by clear * - h hAB hAC hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hBn hq0; omega)
              · exact Or.inr (by clear * - h hAD hCn hApos; omega)
              · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
            rcases hbdeltas with h | h
            · exact Or.inl h
            · exact Or.inr (by clear * - h hq0 hApos; omega)
          have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hq1; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hBn hq1; omega)
            · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by clear * - h hAD hCn hApos; omega)
            · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
            · exact Or.inr (by clear * - h hAD hCn hApos; omega)
            · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
            · exact Or.inr (by clear * - h hq1; omega)
            · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          have hrest : (kappaQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
              A B C D E F G).natDegree < D.natDegree + E.natDegree :=
            kappaQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
              A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega))
          have hlead : (kappaQuarticChamberFace8000810 A B C D E F G).natDegree =
              D.natDegree + E.natDegree :=
            kappaQuarticChamberFace8000810_natDegree A B C D E F G hDne hEne
          rw [degreeZeroKappaQuartic810_eq_face8000_add_rest,
            natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
            at hkap
          omega
    ·
      have hdpos : A.natDegree < A.natDegree + D.natDegree + G.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + D.natDegree + G.natDegree := by omega
      obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
        quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA homi hnu hkap
      have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hAC hBn hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1 hq2; omega)
      have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hCn hq2; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
        rcases hbdeltas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq2 hApos; omega)
      have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbzetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq2 hApos; omega)
      have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hCn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hCn hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hCn hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
        rcases hbthetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0; omega)
      have hrest : (n3QuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + D.natDegree + G.natDegree :=
        n3QuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by omega) (by omega) (by clear * - hq1; omega) hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega)) hztheta
      have hlead : (n3QuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + D.natDegree + G.natDegree :=
        n3QuarticChamberFace8000810_natDegree A B C D E F G hAne hDne hGne
      have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
        A B C D E F G hApos homi hnu
      rw [degreeZeroN3Quartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hle
      omega
    ·
      have hdpos : A.natDegree < A.natDegree + D.natDegree + G.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + D.natDegree + G.natDegree := by omega
      obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
        quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA homi hnu hkap
      have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hAC hBn hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1 hq2; omega)
      have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hCn hq2; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
        rcases hbdeltas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq2 hApos; omega)
      have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbzetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq2 hApos; omega)
      have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hCn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hCn hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hCn hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
        rcases hbthetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0; omega)
      have hrest : (n3QuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + D.natDegree + G.natDegree :=
        n3QuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by omega) (by omega) (by clear * - hq1; omega) hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega)) hztheta
      have hlead : (n3QuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + D.natDegree + G.natDegree :=
        n3QuarticChamberFace8000810_natDegree A B C D E F G hAne hDne hGne
      have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
        A B C D E F G hApos homi hnu
      rw [degreeZeroN3Quartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hle
      omega
  ·
    rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (2 * D.natDegree + E.natDegree) with hpv | hpv | hpv
    ·
      have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + 2 * D.natDegree := by omega
      obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
        quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hAD; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hApos; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq1; omega)
      have hrest : (muQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
        muQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by clear * - hq1; omega) (by clear * - hq0; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
      have hlead : (muQuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + 2 * D.natDegree :=
        muQuarticChamberFace8000810_natDegree A B C D E F G hAne hDne
      rw [degreeZeroMuQuartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hmuDeg
      omega
    ·
      have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + 2 * D.natDegree := by omega
      obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
        quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hAD; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hApos; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq1; omega)
      have hrest : (muQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
        muQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by clear * - hq1; omega) (by clear * - hq0; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
      have hlead : (muQuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + 2 * D.natDegree :=
        muQuarticChamberFace8000810_natDegree A B C D E F G hAne hDne
      rw [degreeZeroMuQuartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hmuDeg
      omega
    ·
      have hdpos : A.natDegree < A.natDegree + D.natDegree + G.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + D.natDegree + G.natDegree := by omega
      obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
        quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA homi hnu hkap
      have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hAC hBn hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1 hq2; omega)
      have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hq1; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hCn hq2; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAC hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
        rcases hbdeltas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq2 hApos; omega)
      have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hq0 hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
        rcases hbzetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq2 hApos; omega)
      have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
        have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hCn hq2 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hCn hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hCn hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hAD hCn hApos; omega)
          · exact Or.inr (by clear * - h hBn hq1 hApos; omega)
          · exact Or.inr (by clear * - h hq1; omega)
          · exact Or.inr (by clear * - h hAC hBn hq1 hApos; omega)
        rcases hbthetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0; omega)
      have hrest : (n3QuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + D.natDegree + G.natDegree :=
        n3QuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by omega) (by omega) (by clear * - hq1; omega) hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega)) hztheta
      have hlead : (n3QuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + D.natDegree + G.natDegree :=
        n3QuarticChamberFace8000810_natDegree A B C D E F G hAne hDne hGne
      have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
        A B C D E F G hApos homi hnu
      rw [degreeZeroN3Quartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hle
      omega
  ·
    rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (2 * D.natDegree + E.natDegree) with hpv | hpv | hpv
    ·
      have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + 2 * D.natDegree := by omega
      obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
        quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hAD; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hApos; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq1; omega)
      have hrest : (muQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
        muQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by clear * - hq1; omega) (by clear * - hq0; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
      have hlead : (muQuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + 2 * D.natDegree :=
        muQuarticChamberFace8000810_natDegree A B C D E F G hAne hDne
      rw [degreeZeroMuQuartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hmuDeg
      omega
    ·
      have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + 2 * D.natDegree := by omega
      obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
        quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hAD; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
        have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - h hApos; omega)
          · exact Or.inr (by clear * - h hAD hq0; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq1; omega)
      have hrest : (muQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
        muQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by clear * - hq1; omega) (by clear * - hq0; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
      have hlead : (muQuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + 2 * D.natDegree :=
        muQuarticChamberFace8000810_natDegree A B C D E F G hAne hDne
      rw [degreeZeroMuQuartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hmuDeg
      omega
    ·
      have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
        omega
      have hdzpos : 0 < A.natDegree + D.natDegree + F.natDegree := by omega
      obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
        quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
        quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hkbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hBn hq0 hq2; omega)
          · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hAC hBn hApos; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1 hq2; omega)
      have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hkbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq1 hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hApos; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq1; omega)
      have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hkbdelta with h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hAD hCn hq1; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hBn hApos; omega)
          · exact Or.inr (by clear * - h hAD hBn hq0; omega)
          · exact Or.inr (by clear * - h hBn hCn hApos; omega)
          · exact Or.inr (by clear * - h hAD hq1; omega)
          · exact Or.inr (by clear * - h hAC hBn hApos; omega)
        rcases hbdeltas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq1; omega)
      have hzzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbzetas : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
          · exact Or.inr (by clear * - h hApos; omega)
          · exact Or.inr (by omega)
        rcases hbzetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq1; omega)
      have hrest : (xiQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
        xiQuarticChamberRest8000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by omega) (by clear * - hq1; omega) hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
      have hlead : (xiQuarticChamberFace8000810 A B C D E F G).natDegree =
          A.natDegree + D.natDegree + F.natDegree :=
        xiQuarticChamberFace8000810_natDegree A B C D E F G hAne hDne hFne
      rw [degreeZeroXiQuartic810_eq_face8000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hxiDeg
      omega


end QuarticChamberUnownedRefine810

end Max11DegreeRoutes
