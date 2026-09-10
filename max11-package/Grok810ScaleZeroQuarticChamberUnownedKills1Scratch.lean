import Grok810ScaleZeroQuarticChamberFacesScratch
import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsScratch
import Grok810ScaleZeroQuarticChamberColumns2Scratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Scratch
import Grok810ScaleZeroQuarticChamberNuFacesScratch
import Grok810ScaleZeroQuarticChamberColumns3Scratch
import Grok810ScaleZeroQuarticChamberRests3Scratch
import Grok810ScaleZeroQuarticChamberKills3Scratch
import Grok810ScaleZeroQuarticChamberRests4Scratch
import Grok810ScaleZeroQuarticChamberInnerScratch
import Grok810ScaleZeroQuarticChamberKills4Scratch
import Grok810ScaleZeroQuarticChamberColumns5Scratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsScratch
import Grok810ScaleZeroQuarticChamberRests6Scratch
import Grok810ScaleZeroQuarticChamberInfraN2Scratch
import Grok810ScaleZeroQuarticChamberInfraN3Scratch
import Grok810ScaleZeroQuarticChamberInfraN4Scratch
import Grok810ScaleZeroQuarticChamberInfraN5Scratch
import Grok810ScaleZeroQuarticChamberInfraN6Scratch
import Grok810ScaleZeroQuarticChamberInfraN7Scratch
import Grok810ScaleZeroQuarticChamberInfraOmicronScratch
import Grok810ScaleZeroQuarticChamberInfraPrimitiveScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberN7BandsScratch
import Grok810ScaleZeroQuarticChamberUnownedPacketsScratch
import Grok810ScaleZeroQuarticChamberUnownedColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns5Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests3Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests4Scratch

/-! # Unowned single-carrier kills, part 1/5

25 of the 85 chambers `UNOWNED_CHAMBERS.md` closes with a
single-monomial face, after the carrier change (including `N₂, N₃,
`N₅`, `N₆`) and the `n5-cost`/`n7-cost` bands.  A column marked
`*-hnc` is discharged by `by_contra` plus the chamber's ℕ conjuncts,
which force every letter constant and contradict `hnc`.
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

section QuarticChamberUnownedKills1810

/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0) :
    (muQuarticChamberFace5000810 A B C D E F G).natDegree =
      3 * C.natDegree := by
  have hc : (-(5 / 128 : k)) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace5000810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace5001810_natDegree
    (A B C D E F G : k[X])
    (hEne : E ≠ 0) :
    (muQuarticChamberFace5001810 A B C D E F G).natDegree =
      2 * E.natDegree := by
  have hc : (5 / 32 : k) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace5001810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hGne : G ≠ 0) :
    (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree := by
  have hc : (5 / 4 : k) ≠ 0 := by norm_num
  simp only [piQuarticChamberFace5000810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0) :
    (n3QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by
  have hc : (45 / 2048 : k) ≠ 0 := by norm_num
  simp only [n3QuarticChamberFace5000810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne)]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hEne : E ≠ 0) :
    (xiQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree := by
  have hc : (-(15 / 128 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace5000810]
  rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace5001810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hFne : F ≠ 0) :
    (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree := by
  have hc : (-(5 / 16 : k)) ≠ 0 := by norm_num
  simp only [piQuarticChamberFace5001810]
  rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hFne)]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hDne : D ≠ 0) :
    (n2QuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + D.natDegree := by
  have hc : (-(15 / 128 : k)) ≠ 0 := by norm_num
  simp only [n2QuarticChamberFace5000810]
  rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hDne]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace5001810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0) :
    (xiQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree := by
  have hc : (-(5 / 64 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace5001810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (kappaQuarticChamberFace5000810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace5000810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberFace5001810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hGne : G ≠ 0) :
    (n2QuarticChamberFace5001810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [n2QuarticChamberFace5001810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hGne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    (n6QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + F.natDegree + G.natDegree := by
  have hc : (-(25 / 48 : k)) ≠ 0 := by norm_num
  simp only [n6QuarticChamberFace5000810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace5001810_natDegree
    (A B C D E F G : k[X])
    (hBne : B ≠ 0)
    (hGne : G ≠ 0) :
    (kappaQuarticChamberFace5001810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace5001810]
  rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace5002810_natDegree
    (A B C D E F G : k[X])
    (hEne : E ≠ 0)
    (hGne : G ≠ 0) :
    (xiQuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace5002810]
  rw [natDegree_smul _ hc, natDegree_mul hEne hGne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberFace5002810_natDegree
    (A B C D E F G : k[X])
    (hEne : E ≠ 0)
    (hFne : F ≠ 0) :
    (n2QuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + F.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [n2QuarticChamberFace5002810]
  rw [natDegree_smul _ hc, natDegree_mul hEne hFne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem n5QuarticChamberFace5000810_natDegree
    (A B C D E F G : k[X])
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    (n5QuarticChamberFace5000810 A B C D E F G).natDegree =
      F.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [n5QuarticChamberFace5000810]
  rw [natDegree_smul _ hc, natDegree_mul hFne hGne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace5002810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hFne : F ≠ 0) :
    (kappaQuarticChamberFace5002810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace5002810]
  rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace5003810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hDne : D ≠ 0) :
    (xiQuarticChamberFace5003810 A B C D E F G).natDegree =
      C.natDegree + 2 * D.natDegree := by
  have hc : (-(15 / 128 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace5003810]
  rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne)]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberFace5003810_natDegree
    (A B C D E F G : k[X])
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0) :
    (n2QuarticChamberFace5003810 A B C D E F G).natDegree =
      B.natDegree + C.natDegree + E.natDegree := by
  have hc : (-(15 / 64 : k)) ≠ 0 := by norm_num
  simp only [n2QuarticChamberFace5003810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
  all_goals omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `C` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberC0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberC0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFz, hGz⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hFn hGn hcon; omega)
  have hh0 : 2 * C.natDegree < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hFn hGn hdpos hcon; omega)
  have hh1 : C.natDegree < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hFn hGn hdpos hcon; omega)
  have hrest : (muQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest5000810_natDegree_lt_of_live_C l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz hFz hGz (Or.inr hh0) (Or.inr hh1)
  have hlead : (muQuarticChamberFace5000810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace5000810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hFn hGn hdpos hmu; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `E` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberE0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberE0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFz, hGz⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hFn hGn hcon; omega)
  have hh0 : E.natDegree < 2 * E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hFn hGn hdpos hcon; omega)
  have hrest : (muQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest5001810_natDegree_lt_of_live_E l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz hFz hGz (Or.inr hh0)
  have hlead : (muQuarticChamberFace5001810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace5001810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  clear * - hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hFn hGn hdpos hmu; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `G` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEz, hFz, hGne⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hEn hFn hcon; omega)
  have hh0 : G.natDegree < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hEn hFn hdpos hcon; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_G l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz hEz hFz (Or.inr hh0)
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hEn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CD` / `DD·CCC` dies on the `N₃` face `A.natDegree + 2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberCD2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCD2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFz, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hGn hcon; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1; omega)
  have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hGn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAF hBn hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1; omega)
  have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hGn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest5000810_natDegree_lt_of_live_CD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hFz hGz (by clear * - hcq0 hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hApos; omega)) hztheta
  have hlead : (n3QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberFace5000810_natDegree A B C D E F G hAne hCne hDne
  have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu
  rw [degreeZeroN3Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hGn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CE` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCE2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCE2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hFn hGn hcon; omega)
  have hh0 : C.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hFn hGn hdpos hcon; omega)
  have hh1 : 2 * C.natDegree < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hFn hGn hdpos hcon; omega)
  have hh2 : E.natDegree < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hFn hGn hdpos hcon; omega)
  have hrest : (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest5000810_natDegree_lt_of_live_CE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz hGz (Or.inr hh0) (Or.inr hh1) (Or.inr hh2)
  have hlead : (xiQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace5000810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hFn hGn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CF` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hApos; omega)
  have hzzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbzeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd hBz h
    · exact Or.inr (by clear * - h hcq1; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact absurd h (by clear * - hEn hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact absurd h (by clear * - hGn hApos; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz hGz (by clear * - hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq1; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hGn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hFn hcon; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz hFz (by clear * - hcq1; omega) (by clear * - hcq1; omega) (Or.inr (by clear * - hcq1; omega)) (Or.inr (by clear * - hcq1; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `FG` / `FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberFG0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberFG0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEz, hFne, hGne, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hEn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hAF; omega)
      · exact Or.inr (by clear * - h hAF hcq0; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAF hcq0; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hApos; omega)
    · exact absurd h (by clear * - hCn hApos; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact absurd h (by clear * - hEn hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hAF hcq0; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hApos; omega)
    · exact absurd h (by clear * - hCn hApos; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact absurd h (by clear * - hEn hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hzzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbzeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd hBz h
    · exact absurd h (by clear * - hCn hApos; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact absurd h (by clear * - hEn hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_FG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz hEz (by clear * - hcq0; omega) hzl hzbeta hzdelta hzzeta (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hEn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCD` / `DD·CCC` dies on the `N₂` face `2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberBCD6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCD6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hApos hAB hAC hAD hAE hAF hAG hEn hFn hGn hcon; omega)
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
  have hztheta : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hGn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hApos; omega)
  have hrest : (n2QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest5000810_natDegree_lt_of_live_BCD l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz hGz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hcq5; omega) (by clear * - hcq0 hcq5; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hztheta
  have hlead : (n2QuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + D.natDegree :=
    n2QuarticChamberFace5000810_natDegree A B C D E F G hCne hDne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hApos hAB hAC hAD hAE hAF hAG hEn hFn hGn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BDF` / `BF·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBDF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hrest : (xiQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest5001810_natDegree_lt_of_live_BDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz hGz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3; omega))
  have hlead : (xiQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace5001810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hEn hGn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BEF` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBEF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hDn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hCn hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_BEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz hGz (by clear * - hcq3; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hzdelta (Or.inr (by clear * - hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq3 hApos; omega)) (Or.inr (by clear * - hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hCn hDn hGn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDE` / `DD·CCC` dies on the `N₃` face `A.natDegree + 2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberCDE2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDE2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hFn hGn hcon; omega)
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAG hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAF hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAG hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hAF hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAG hBn hGn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hGn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hBn hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hGn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hApos; omega)
  have hrest : (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest5000810_natDegree_lt_of_live_CDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hGz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1; omega)) hztheta
  have hlead : (n3QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberFace5000810_natDegree A B C D E F G hAne hCne hDne
  have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu
  rw [degreeZeroN3Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hFn hGn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDE` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCDE6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDE6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hFn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hrest : (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest5000810_natDegree_lt_of_live_CDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz hGz (by clear * - hcq0 hcq1 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega))
  have hlead : (xiQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace5000810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hFn hGn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDF` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hApos; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hGz (by clear * - hcq0 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hGn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDF` / `DD·CCC` dies on the `N₃` face `A.natDegree + 2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberCDF8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDF8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hGn hcon; omega)
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hAG hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hAG hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAG hGn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAG hBn hGn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hGn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hGn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hrest : (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest5000810_natDegree_lt_of_live_CDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hGz (by clear * - hcq2; omega) (by clear * - hcq0 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hztheta
  have hlead : (n3QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberFace5000810_natDegree A B C D E F G hAne hCne hDne
  have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu
  rw [degreeZeroN3Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hGn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq3; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hFz (by clear * - hcq0 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hFz (by clear * - hcq0 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq3; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDG` / `DD·CCC` dies on the `N₃` face `A.natDegree + 2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberCDG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hcon; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq4; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hrest : (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest5000810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hFz (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1; omega)) hztheta
  have hlead : (n3QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberFace5000810_natDegree A B C D E F G hAne hCne hDne
  have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu
  rw [degreeZeroN3Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hEn hFn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEF` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCEF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq3; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hApos; omega)
  have hzzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbzeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd hBz h
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq1 hcq3; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact absurd h (by clear * - hGn hApos; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hcq3; omega) (by clear * - hcq0 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq3; omega)) hzzeta (Or.inr (by clear * - hcq3; omega)) (Or.inr (by clear * - hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hGn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEF` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCEF8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEF8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
      · exact absurd h (by clear * - hGn hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4; omega)
  have hzdelta : delta = 0 ∨ (A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact absurd h (by clear * - hDn hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    · exact absurd h (by clear * - hGn hcq0 hcq1 hcq4; omega)
  have hrest : (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest5000810_natDegree_lt_of_live_CEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hGz (by clear * - hcq0 hcq1 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4; omega))
  have hlead : (xiQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace5000810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hGn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCEG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hFn hcon; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by clear * - hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq3; omega) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq3; omega)) (Or.inr (by clear * - hcq3; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CFG` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq4; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq4; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hApos; omega)
  have hzzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbzeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd hBz h
    · exact Or.inr (by clear * - h hcq4; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact absurd h (by clear * - hEn hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz (by clear * - hcq4; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0; omega) hzl hzbeta (Or.inr (by clear * - hcq4; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq0 hcq4; omega)) (Or.inr (by clear * - hcq4 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CFG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCFG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq4; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz (by clear * - hcq4; omega) (by clear * - hcq0; omega) (by clear * - hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq4; omega)) hzdelta (Or.inr (by clear * - hcq0; omega)) (Or.inr (by clear * - hcq4; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hDn hEn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DEG` / `EE` dies on the `κ` face `D.natDegree + E.natDegree`. -/
theorem quarticChamberDEG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hCn hFn hcon; omega)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAE hFn hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq3 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq0 hcq3; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAE hFn hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hCn hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq3 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq3; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hAE hFn hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hCn hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq3 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0; omega)
      · exact Or.inr (by clear * - h hBn hcq3 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hAE hFn hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq0; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq3 hApos; omega)
  have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3; omega)
    · exact Or.inr (by clear * - h hFn hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hFn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAE hCn hcq0; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hBn hApos; omega)
    · exact Or.inr (by clear * - h hAE hCn hcq0; omega)
    · exact Or.inr (by clear * - h hBn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hFn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq3 hApos; omega)
    · exact Or.inr (by clear * - h hAE hcq0; omega)
  have hrest : (kappaQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest5000810_natDegree_lt_of_live_DEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hFz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hApos; omega)) hzzeta hztheta
  have hlead : (kappaQuarticChamberFace5000810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace5000810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hCn hFn hdpos hkap; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DFG` / `DD·DF·DG·FF·FG·GG` dies on the `N₂` face `D.natDegree + G.natDegree`. -/
theorem quarticChamberDFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hCn hEn hcon; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hEn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq1; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hEn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq1; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hEn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hApos; omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree) := by
    rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hEn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hAD hBn hCn hcq0 hcq1; omega)
    · exact Or.inr (by clear * - h hAD hAE hBn hEn hcq1; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hEn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hAD hCn hcq1; omega)
    · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1; omega)
    · exact Or.inr (by clear * - h hAD hAE hEn hcq1; omega)
    · exact Or.inr (by clear * - h hAB hAD hBn hcq1; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq1 hApos; omega)
  have hztheta : theta = 0 ∨ (2 * A.natDegree < D.natDegree + G.natDegree) := by
    rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hEn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hEn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hEn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hAD hCn hcq1; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
  have hrest : (n2QuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    n2QuarticChamberRest5001810_natDegree_lt_of_live_DFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hEz hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzzeta (Or.inr (by clear * - hcq1 hApos; omega)) hztheta
  have hlead : (n2QuarticChamberFace5001810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    n2QuarticChamberFace5001810_natDegree A B C D E F G hDne hGne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hCn hEn hdpos hle; omega


end QuarticChamberUnownedKills1810

end Max11DegreeRoutes
