import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN7BandsScratch
import Grok810ScaleZeroQuarticChamberUnownedSplitRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems9Part2Scratch

/-! # Unowned letter splits and load trichotomies, `(8,10)` scale zero

6 chambers of `UNOWNED_CHAMBERS.md` §3.2/§3.4 that need a case
distinction: an `n_X = 0` split or an `lt_trichotomy` against a load
column, with a single-carrier kill on every branch.  Every branch
verdict is an exact rational Farkas certificate on the sub-chamber.
Untracked working note.
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

section QuarticChamberUnownedSplits810

/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace7000810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0) :
    (muQuarticChamberFace7000810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree := by
  have hc : (-(5 / 128 : k)) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace7000810]
  rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne)]
  simp only [natDegree_pow]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace7000810_natDegree
    (A B C D E F G : k[X])
    (hGne : G ≠ 0) :
    (piQuarticChamberFace7000810 A B C D E F G).natDegree =
      2 * G.natDegree := by
  have hc : (5 / 4 : k) ≠ 0 := by norm_num
  simp only [piQuarticChamberFace7000810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace7001810_natDegree
    (A B C D E F G : k[X])
    (hEne : E ≠ 0) :
    (muQuarticChamberFace7001810 A B C D E F G).natDegree =
      2 * E.natDegree := by
  have hc : (5 / 32 : k) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace7001810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace7000810_natDegree
    (A B C D E F G : k[X])
    (hFne : F ≠ 0) :
    (xiQuarticChamberFace7000810 A B C D E F G).natDegree =
      2 * F.natDegree := by
  have hc : (5 / 32 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace7000810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace7001810_natDegree
    (A B C D E F G : k[X])
    (hEne : E ≠ 0)
    (hGne : G ≠ 0) :
    (xiQuarticChamberFace7001810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace7001810]
  rw [natDegree_smul _ hc, natDegree_mul hEne hGne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace7002810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0) :
    (xiQuarticChamberFace7002810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree := by
  have hc : (-(5 / 64 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace7002810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace7000810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (kappaQuarticChamberFace7000810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace7000810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace7002810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hGne : G ≠ 0) :
    (muQuarticChamberFace7002810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace7002810]
  rw [natDegree_smul _ hc, natDegree_mul hCne hGne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberFace7000810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hGne : G ≠ 0) :
    (n2QuarticChamberFace7000810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [n2QuarticChamberFace7000810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hGne]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberFace7000810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    (n6QuarticChamberFace7000810 A B C D E F G).natDegree =
      A.natDegree + F.natDegree + G.natDegree := by
  have hc : (-(25 / 48 : k)) ≠ 0 := by norm_num
  simp only [n6QuarticChamberFace7000810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne]
  all_goals omega

/-! ## The split and trichotomy kills -/

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DG` / `DD` dies on a load trichotomy with 3 branches. -/
theorem quarticChamberDG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEz, hFz, hGne, hq0, hq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * D.natDegree) with hpv | hpv | hpv
  ·
    have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
      omega
    have hdzpos : 0 < A.natDegree + 2 * D.natDegree := by omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hAD; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hAD hq0; omega)
    have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hAD hq0; omega)
    have hzdelta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact absurd h (by clear * - hFn hApos; omega)
      · exact Or.inr (by clear * - h hq0 hApos; omega)
    have hrest : (muQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
      muQuarticChamberRest7000810_natDegree_lt_of_live_DG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hEz hFz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hApos; omega))
    have hlead : (muQuarticChamberFace7000810 A B C D E F G).natDegree =
        A.natDegree + 2 * D.natDegree :=
      muQuarticChamberFace7000810_natDegree A B C D E F G hAne hDne
    rw [degreeZeroMuQuartic810_eq_face7000_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hmuDeg
    omega
  ·
    have hdpos : 0 < 2 * G.natDegree := by
      omega
    have hdzpos : 0 < 2 * G.natDegree := by omega
    have hrest : (piQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < 2 * G.natDegree :=
      piQuarticChamberRest7000810_natDegree_lt_of_live_DG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hEz hFz (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hdzpos; omega))
    have hlead : (piQuarticChamberFace7000810 A B C D E F G).natDegree =
        2 * G.natDegree :=
      piQuarticChamberFace7000810_natDegree A B C D E F G hGne
    rw [degreeZeroPiQuartic810_eq_face7000_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hpiDeg
    omega
  ·
    have hdpos : 0 < 2 * G.natDegree := by
      omega
    have hdzpos : 0 < 2 * G.natDegree := by omega
    have hrest : (piQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < 2 * G.natDegree :=
      piQuarticChamberRest7000810_natDegree_lt_of_live_DG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hEz hFz (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hdzpos; omega))
    have hlead : (piQuarticChamberFace7000810 A B C D E F G).natDegree =
        2 * G.natDegree :=
      piQuarticChamberFace7000810_natDegree A B C D E F G hGne
    rw [degreeZeroPiQuartic810_eq_face7000_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hpiDeg
    omega

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `EF` / `EE` dies on a letter split with 2 branches. -/
theorem quarticChamberEF0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberEF0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFne, hGz, hq0, hq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  by_cases hs0 : 0 < E.natDegree
  ·
    have hdpos : 0 < 2 * E.natDegree := by
      omega
    have hdzpos : 0 < 2 * E.natDegree := by omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hAE hq0; omega)
      · exact Or.inr (by clear * - h hAE hq0; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    have hzbeta : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hq0 hApos; omega)
      · exact Or.inr (by clear * - h hAE hq0; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    have hzdelta : delta = 0 ∨ (F.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hq0 hApos; omega)
      · exact Or.inr (by clear * - h hq0 hApos; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    have hrest : (muQuarticChamberRest7001810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < 2 * E.natDegree :=
      muQuarticChamberRest7001810_natDegree_lt_of_live_EF l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hDz hGz hzl hzbeta hzdelta (Or.inr (by clear * - hdzpos; omega))
    have hlead : (muQuarticChamberFace7001810 A B C D E F G).natDegree =
        2 * E.natDegree :=
      muQuarticChamberFace7001810_natDegree A B C D E F G hEne
    rw [degreeZeroMuQuartic810_eq_face7001_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hmuDeg
    omega
  ·
    have hs0z : E.natDegree = 0 := by omega
    have hdpos : 0 < 2 * F.natDegree := by
      by_contra hcon
      exact hnc (by omega)
    have hdzpos : 0 < 2 * F.natDegree := by omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨(by by_contra hcon; exact hnc (by omega)), (by by_contra hcon; exact hnc (by omega))⟩
      · exact Or.inr ⟨(by by_contra hcon; exact hnc (by omega)), (by by_contra hcon; exact hnc (by omega))⟩
      · exact Or.inr ⟨(by by_contra hcon; exact hnc (by omega)), (by by_contra hcon; exact hnc (by omega))⟩
      · exact Or.inr ⟨(by by_contra hcon; exact hnc (by omega)), (by by_contra hcon; exact hnc (by omega))⟩
      · exact Or.inr ⟨(by by_contra hcon; exact hnc (by omega)), (by by_contra hcon; exact hnc (by omega))⟩
      · exact Or.inr ⟨(by by_contra hcon; exact hnc (by omega)), (by by_contra hcon; exact hnc (by omega))⟩
    have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by omega)
      · exact Or.inr (by clear * - h hAE hq0; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    have hzdelta : delta = 0 ∨ (A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    have hh0 : F.natDegree < 2 * F.natDegree := by
      by_contra hcon
      exact hnc (by omega)
    have hh1 : E.natDegree < 2 * F.natDegree := by
      by_contra hcon
      exact hnc (by omega)
    have hrest : (xiQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < 2 * F.natDegree :=
      xiQuarticChamberRest7000810_natDegree_lt_of_live_EF l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hDz hGz hzl hzbeta hzdelta (Or.inr hh0) (Or.inr hh1)
    have hlead : (xiQuarticChamberFace7000810 A B C D E F G).natDegree =
        2 * F.natDegree :=
      xiQuarticChamberFace7000810_natDegree A B C D E F G hFne
    rw [degreeZeroXiQuartic810_eq_face7000_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hxiDeg
    omega

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `EG` / `EE` dies on a letter split with 4 branches. -/
theorem quarticChamberEG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberEG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFz, hGne, hq0, hq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  by_cases hs0 : 0 < E.natDegree
  ·
    by_cases hs1 : 0 < G.natDegree
    ·
      have hdpos : 0 < E.natDegree + G.natDegree := by
        omega
      have hdzpos : 0 < E.natDegree + G.natDegree := by omega
      have hrest : (xiQuarticChamberRest7001810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < E.natDegree + G.natDegree :=
        xiQuarticChamberRest7001810_natDegree_lt_of_live_EG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz hDz hFz (Or.inr (by omega)) (Or.inr (by omega))
      have hlead : (xiQuarticChamberFace7001810 A B C D E F G).natDegree =
          E.natDegree + G.natDegree :=
        xiQuarticChamberFace7001810_natDegree A B C D E F G hEne hGne
      rw [degreeZeroXiQuartic810_eq_face7001_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hxiDeg
      omega
    ·
      have hs1z : G.natDegree = 0 := by omega
      have hdpos : 0 < 2 * E.natDegree := by
        omega
      have hdzpos : 0 < 2 * E.natDegree := by omega
      have hrest : (muQuarticChamberRest7001810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < 2 * E.natDegree :=
        muQuarticChamberRest7001810_natDegree_lt_of_live_EG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz hDz hFz (Or.inr (by omega)) (Or.inr (by clear * - hdzpos; omega))
      have hlead : (muQuarticChamberFace7001810 A B C D E F G).natDegree =
          2 * E.natDegree :=
        muQuarticChamberFace7001810_natDegree A B C D E F G hEne
      rw [degreeZeroMuQuartic810_eq_face7001_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hmuDeg
      omega
  ·
    have hs0z : E.natDegree = 0 := by omega
    by_cases hs1 : 0 < G.natDegree
    ·
      have hdpos : 0 < 2 * G.natDegree := by
        omega
      have hdzpos : 0 < 2 * G.natDegree := by omega
      have hrest : (piQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < 2 * G.natDegree :=
        piQuarticChamberRest7000810_natDegree_lt_of_live_EG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz hDz hFz (Or.inr (by omega)) (Or.inr (by clear * - hdzpos; omega))
      have hlead : (piQuarticChamberFace7000810 A B C D E F G).natDegree =
          2 * G.natDegree :=
        piQuarticChamberFace7000810_natDegree A B C D E F G hGne
      rw [degreeZeroPiQuartic810_eq_face7000_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hpiDeg
      omega
    ·
      have hs1z : G.natDegree = 0 := by omega
      have hdpos : 0 < 2 * E.natDegree := by
        by_contra hcon
        exact hnc (by omega)
      have hdzpos : 0 < 2 * E.natDegree := by omega
      have hh0 : G.natDegree < 2 * E.natDegree := by
        by_contra hcon
        exact hnc (by omega)
      have hh1 : E.natDegree < 2 * E.natDegree := by
        by_contra hcon
        exact hnc (by omega)
      have hrest : (muQuarticChamberRest7001810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < 2 * E.natDegree :=
        muQuarticChamberRest7001810_natDegree_lt_of_live_EG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz hDz hFz (Or.inr hh0) (Or.inr hh1)
      have hlead : (muQuarticChamberFace7001810 A B C D E F G).natDegree =
          2 * E.natDegree :=
        muQuarticChamberFace7001810_natDegree A B C D E F G hEne
      rw [degreeZeroMuQuartic810_eq_face7001_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hmuDeg
      omega

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DEF` / `DD·DE·EE` dies on a load trichotomy with 3 branches. -/
theorem quarticChamberDEF2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEF2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  rcases lt_trichotomy (D.natDegree) (A.natDegree + F.natDegree) with hpv | hpv | hpv
  ·
    have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
      omega
    have hdzpos : 0 < A.natDegree + D.natDegree + F.natDegree := by omega
    obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
      quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hnu hkap
    have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        rcases hnbl with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq2; omega)
        · exact Or.inr (by clear * - h hAD hq0; omega)
        · exact Or.inr (by clear * - h hAD hBn hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAC hAD hBn hq0 hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq2; omega)
        · exact Or.inr (by clear * - h hAD hCn hq2; omega)
        · exact Or.inr (by clear * - h hAC hBn hApos; omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
    have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        rcases hnbbeta with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq2; omega)
        · exact Or.inr (by clear * - h hAD hq0; omega)
        · exact Or.inr (by clear * - h hAD hBn hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hCn hq0 hq2; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by clear * - h hAD hCn hq2; omega)
        · exact Or.inr (by clear * - h hAC hBn hApos; omega)
      rcases hbbetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
    have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq2; omega)
        · exact Or.inr (by clear * - h hAD hq0; omega)
        · exact Or.inr (by clear * - h hAD hBn hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hCn hq0 hq2; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by clear * - h hAD hCn hq2; omega)
        · exact Or.inr (by clear * - h hAC hBn hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2; omega)
        · exact Or.inr (by clear * - h hAD hCn hq2; omega)
        · exact Or.inr (by clear * - h hBn hApos; omega)
      rcases hbdeltas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq2; omega)
    have hzzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      have hbzetas : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hApos; omega)
        · exact Or.inr (by clear * - h hAD hq0; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by clear * - h hAD hBn hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hCn hq0; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by clear * - h hAD hCn hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0; omega)
        · exact Or.inr (by clear * - h hAD hCn hApos; omega)
        · exact Or.inr (by clear * - h hBn hApos; omega)
        · exact Or.inr (by clear * - h hAD hq2; omega)
        · exact Or.inr (by clear * - h hAB hAC hBn; omega)
      rcases hbzetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq2; omega)
    have hrest : (xiQuarticChamberRest7002810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
      xiQuarticChamberRest7002810_natDegree_lt_of_live_DEF l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hGz (by clear * - hq2; omega) hzl hzbeta (Or.inr (by omega)) hzdelta hzzeta (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
    have hlead : (xiQuarticChamberFace7002810 A B C D E F G).natDegree =
        A.natDegree + D.natDegree + F.natDegree :=
      xiQuarticChamberFace7002810_natDegree A B C D E F G hAne hDne hFne
    rw [degreeZeroXiQuartic810_eq_face7002_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hxiDeg
    omega
  ·
    have hdpos : 0 < D.natDegree + E.natDegree := by
      omega
    have hdzpos : 0 < D.natDegree + E.natDegree := by omega
    obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
      quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hnu hkap
    have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
      have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbl with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq2 hApos; omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0; omega)
    have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree) := by
      have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbbeta with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq2 hApos; omega)
      rcases hbbetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0; omega)
    have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
      have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
        · exact Or.inr (by clear * - h hAC hAD hCn hq0; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
      rcases hbdeltas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hApos; omega)
    have hrest : (kappaQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < D.natDegree + E.natDegree :=
      kappaQuarticChamberRest7000810_natDegree_lt_of_live_DEF l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hGz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hq0 hApos hdzpos; omega)) (Or.inr (by omega)) (Or.inr (by omega))
    have hlead : (kappaQuarticChamberFace7000810 A B C D E F G).natDegree =
        D.natDegree + E.natDegree :=
      kappaQuarticChamberFace7000810_natDegree A B C D E F G hDne hEne
    rw [degreeZeroKappaQuartic810_eq_face7000_add_rest,
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
    have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
      have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbl with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq2 hApos; omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0; omega)
    have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree) := by
      have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbbeta with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq2 hApos; omega)
      rcases hbbetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0; omega)
    have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
      have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hGn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
        · exact Or.inr (by clear * - h hAC hAD hCn hq0; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
      rcases hbdeltas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hApos; omega)
    have hrest : (kappaQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < D.natDegree + E.natDegree :=
      kappaQuarticChamberRest7000810_natDegree_lt_of_live_DEF l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hGz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hq0 hApos hdzpos; omega)) (Or.inr (by omega)) (Or.inr (by omega))
    have hlead : (kappaQuarticChamberFace7000810 A B C D E F G).natDegree =
        D.natDegree + E.natDegree :=
      kappaQuarticChamberFace7000810_natDegree A B C D E F G hDne hEne
    rw [degreeZeroKappaQuartic810_eq_face7000_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hkap
    omega

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDFG` / `CF·CG` dies on a letter split with 2 branches. -/
theorem quarticChamberCDFG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG3810 A B C D E F G)
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
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  by_cases hs0 : 0 < C.natDegree
  ·
    have hdpos : 0 < C.natDegree + G.natDegree := by
      omega
    have hdzpos : 0 < C.natDegree + G.natDegree := by omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
        rcases hbl with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
        · exact absurd h (by clear * - hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
    have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hq0 hq3 hq5 hq7; omega)
      · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
      · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
      · exact absurd h (by clear * - hEn hq0 hq3 hq5 hq7; omega)
      · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
      · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
    have hrest : (muQuarticChamberRest7002810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < C.natDegree + G.natDegree :=
      muQuarticChamberRest7002810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hEz (by clear * - hq0 hq1; omega) (by clear * - hq0 hq7; omega) (by clear * - hq0 hq3; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by clear * - hq0 hq1 hq3; omega)) (Or.inr (by clear * - hq0 hq1 hq3 hq7; omega)) (Or.inr (by clear * - hq0 hq1 hq3 hq7; omega))
    have hlead : (muQuarticChamberFace7002810 A B C D E F G).natDegree =
        C.natDegree + G.natDegree :=
      muQuarticChamberFace7002810_natDegree A B C D E F G hCne hGne
    rw [degreeZeroMuQuartic810_eq_face7002_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hmuDeg
    omega
  ·
    have hs0z : C.natDegree = 0 := by omega
    have hdpos : A.natDegree < D.natDegree + G.natDegree := by
      omega
    have hdzpos : 0 < D.natDegree + G.natDegree := by omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
      quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hprim homi hnu hkap
    have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ 3 * C.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree) := by
      have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
        rcases hbl with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact absurd h (by clear * - hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
    have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
      have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
        rcases hbbeta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact absurd h (by clear * - hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbbetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
    have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * C.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
      have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
        rcases hbdelta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact absurd h (by clear * - hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbdeltas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
    have hzzeta : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + G.natDegree) := by
      have hbzetas : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree) := by
        rcases hbzeta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd hBz h
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact absurd h (by clear * - hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbzetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
    have hztheta : theta = 0 ∨ (2 * A.natDegree < D.natDegree + G.natDegree ∧ C.natDegree < D.natDegree + G.natDegree) := by
      have hbthetas : theta = 0 ∨ (2 * A.natDegree < D.natDegree + G.natDegree) := by
        rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hBn hq0 hq7; omega)
        · exact Or.inr (by clear * - h hBn hEn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq5 hq7; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by clear * - h hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hEn hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hEn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hEn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hAE hBn hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq7; omega)
        · exact Or.inr (by clear * - h hBn hEn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hEn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hBn hEn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hAE hEn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hAB hBn hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hAB hBn hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hAB hBn hq0 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hAE hBn hq0 hq3 hq4 hq7; omega)
        · exact Or.inr (by clear * - h hq0 hq3 hq5 hq7; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq3 hq4 hq7; omega)
      rcases hbthetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq5 hq7; omega)
    have hrest : (n2QuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < D.natDegree + G.natDegree :=
      n2QuarticChamberRest7000810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hEz (by clear * - hq0 hq7; omega) hzl hzbeta (Or.inr (by clear * - hq0 hq1 hq3 hq7; omega)) hzdelta (Or.inr (by clear * - hq0 hApos; omega)) hzzeta (Or.inr (by clear * - hq0 hq1 hq3 hq7; omega)) hztheta
    have hlead : (n2QuarticChamberFace7000810 A B C D E F G).natDegree =
        D.natDegree + G.natDegree :=
      n2QuarticChamberFace7000810_natDegree A B C D E F G hDne hGne
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    rw [degreeZeroN2Quartic810_eq_face7000_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hle
    omega

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEFG` / `CF·CG` dies on a letter split with 2 branches. -/
theorem quarticChamberCDEFG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG3810 A B C D E F G)
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
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  by_cases hs0 : 0 < C.natDegree
  ·
    have hdpos : 0 < C.natDegree + G.natDegree := by
      omega
    have hdzpos : 0 < C.natDegree + G.natDegree := by omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + G.natDegree) := by
      have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
        rcases hbl with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq6 hq9 hq11; omega)
    have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hq0 hq4 hq9 hq11; omega)
      · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
      · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
      · exact Or.inr (by clear * - h hq0 hq4 hq6 hq9 hq11; omega)
      · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
      · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
    have hrest : (muQuarticChamberRest7002810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < C.natDegree + G.natDegree :=
      muQuarticChamberRest7002810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz (by clear * - hq0 hq1; omega) (by clear * - hq0 hq11; omega) (by clear * - hq0 hq4; omega) (by clear * - hq0 hq5; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by clear * - hq0 hq1 hq4; omega)) (Or.inr (by clear * - hq0 hq2 hq4 hq6 hq11; omega)) (Or.inr (by clear * - hq0 hq1 hq4 hq11; omega)) (Or.inr (by clear * - hq0 hq1 hq4 hq11; omega))
    have hlead : (muQuarticChamberFace7002810 A B C D E F G).natDegree =
        C.natDegree + G.natDegree :=
      muQuarticChamberFace7002810_natDegree A B C D E F G hCne hGne
    rw [degreeZeroMuQuartic810_eq_face7002_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hmuDeg
    omega
  ·
    have hs0z : C.natDegree = 0 := by omega
    have hdpos : 2 * A.natDegree < A.natDegree + F.natDegree + G.natDegree := by
      omega
    have hdzpos : 0 < A.natDegree + F.natDegree + G.natDegree := by omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
      quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hprim homi hnu hkap
    have hzl : l = 0 ∨ (8 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 6 * A.natDegree + C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 5 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree + F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + E.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * C.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ C.natDegree + D.natDegree + F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ C.natDegree + 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * D.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * G.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      have hbls : l = 0 ∨ (8 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
        rcases hbl with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq4 hq6 hq9 hq11; omega)
    have hzbeta : beta = 0 ∨ (7 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * C.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      have hbbetas : beta = 0 ∨ (7 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
        rcases hbbeta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbbetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq4 hq6 hq9 hq11; omega)
    have hzdelta : delta = 0 ∨ (6 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      have hbdeltas : delta = 0 ∨ (6 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
        rcases hbdelta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbdeltas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq4 hq6 hq9 hq11; omega)
    have hzzeta : zeta = 0 ∨ (5 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      have hbzetas : zeta = 0 ∨ (5 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
        rcases hbzeta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd hBz h
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      rcases hbzetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq4 hq6 hq9 hq11; omega)
    have hztheta : theta = 0 ∨ (4 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * C.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      have hbthetas : theta = 0 ∨ (4 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
        rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hBn hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq2 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq6 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq2 hq6 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq6 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hAB hBn hq0 hq4 hq8 hq11; omega)
        · exact Or.inr (by clear * - h hAB hBn hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hAB hBn hq0 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hAB hBn hq0 hq6 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hq0 hq4 hq9 hq11; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq4 hq8 hq11; omega)
      rcases hbthetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq6 hq9 hq11; omega)
    have hrest : (n6QuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < A.natDegree + F.natDegree + G.natDegree :=
      n6QuarticChamberRest7000810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz (by clear * - hq0 hq11; omega) (by clear * - hq0 hq2 hq11; omega) (by clear * - hq0 hq1 hq4 hq11; omega) (by clear * - hq0 hq4 hq11; omega) (by clear * - hq0 hq4 hq11; omega) (by clear * - hq0 hq6 hq11; omega) (by clear * - hq0 hq4 hq11; omega) (by clear * - hq0 hq2 hq6 hq11; omega) hzl hzbeta (Or.inr (by clear * - hq0 hq1 hq2 hq4 hq6 hq11 hApos; omega)) hzdelta (Or.inr (by clear * - hq0 hq1 hq2 hq4 hq11 hApos; omega)) hzzeta (Or.inr (by clear * - hq0 hq1 hq4 hq11; omega)) hztheta
    have hlead : (n6QuarticChamberFace7000810 A B C D E F G).natDegree =
        A.natDegree + F.natDegree + G.natDegree :=
      n6QuarticChamberFace7000810_natDegree A B C D E F G hAne hFne hGne
    have hle := degreeZeroN6Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi hnu
    rw [degreeZeroN6Quartic810_eq_face7000_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hle
    omega


end QuarticChamberUnownedSplits810

end Max11DegreeRoutes
