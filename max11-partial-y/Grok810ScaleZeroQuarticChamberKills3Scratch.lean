import Grok810ScaleZeroQuarticChamberKills3SpeedTPart00Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Part101Scratch
import Grok810ScaleZeroQuarticChamberRests3Scratch

/-! # Carrier-change chamber kills, `(8,10)` scale zero

The certificate carrier is not sacred: any integral whose face on the chamber is a single monomial kills it once all eight load columns clear.  `π` and `ξ` have `γ`/`ε` columns of letter count ≥ 2, which is what corner `H` needs (plan §2.4).  Decided by `scripts/derive_810_quartic_chamber_killplan3.py`.  Untracked working note.
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

section QuarticChamberKills3810

/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace1000810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hGne : G ≠ 0) :
    (nuQuarticChamberFace1000810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [nuQuarticChamberFace1000810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hGne]
  all_goals omega

/-! ## The chamber kills unblocked by the cost ladder -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the dominated band(s). -/
theorem quarticChamberCG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCG3810 A B C D E F G)
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
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0000 hcq1 hBn hDn hEn hFn hzero)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz hFz (by exact chamberKills3SpeedTArith0001 hcq1) (by exact chamberKills3SpeedTArith0002 hcq1) (Or.inr (by exact chamberKills3SpeedTArith0003 hApos hcq1 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0004 hApos hcq0))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEz, hFne, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0005 hApos hAD hBn hCn hEn hGn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0012 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
    · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
    · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hGn)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0018 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hCn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0019 hApos h hcq0)
    · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hEn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0020 hApos h)
    · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hGn)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_DF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hEz hGz hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0021 hApos hcq0)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0022 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0023 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0024 hApos hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DG` / `DD·DG·GG` dies on the `π` face `2 * G.natDegree`, using the dominated band(s). -/
theorem quarticChamberDG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEz, hFz, hGne, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0025 hApos hcq0 hAD hBn hCn hEn hFn hzero)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_DG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hEz hFz (Or.inr (by exact chamberKills3SpeedTArith0026 hApos hcq0 hAD)) (Or.inr (by exact chamberKills3SpeedTArith0027 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0028 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0029 hApos hcq0))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `EF` / `EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberEF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberEF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFne, hGz, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0030 hApos hAE hBn hCn hDn hGn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0031 h hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0032 h hAE hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0033 h hAE)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
    · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hDn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0034 hApos h hcq0)
    · exact Or.inr (by exact chamberKills3SpeedTArith0035 hApos h)
    · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hGn)
  have hzdelta : delta = 0 ∨ (A.natDegree + F.natDegree < 2 * F.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0018 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hCn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hDn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0036 hApos h hcq0)
    · exact Or.inr (by exact chamberKills3SpeedTArith0037 hApos h)
    · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hGn)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_EF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz hGz hzl hzbeta hzdelta (Or.inr (by exact chamberKills3SpeedTArith0038 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0039 hApos hcq0))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `EG` / `EE·EG·GG` dies on the `π` face `2 * G.natDegree`, using the dominated band(s). -/
theorem quarticChamberEG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberEG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFz, hGne, hcq0, hcq1⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0040 hApos hAE hBn hCn hDn hFn hcq0 hzero)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_EG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz hFz (Or.inr (by exact chamberKills3SpeedTArith0041 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0042 hApos hcq0))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `BDF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBDF9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDF9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
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
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0043 hApos hAB hcq4 hAD hCn hEn hGn hcq3 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0045 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz hGz (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0050 hApos hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0051 hApos hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0052 hApos hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0053 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0054 hApos hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0055 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0056 hApos hcq0 hcq2))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDF` / `CF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDF5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDF5810 A B C D E F G)
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
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0057 hcq0 hcq3 hBn hEn hGn hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0058 h hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0059 h hcq1 hcq4)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0060 h hcq0 hcq1 hcq4)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0061 hcq0 h hcq1 hcq4)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0062 h hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0063 h hcq1 hcq4)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0064 h hcq0 hcq1 hcq4)
      · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0065 hcq0 h hcq1 hcq4)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hGz (by exact chamberKills3SpeedTArith0066 hcq0 hcq1 hcq4) (by exact chamberKills3SpeedTArith0067 hcq4 hcq1) (by exact chamberKills3SpeedTArith0068 hcq4) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0069 hApos hcq0 hcq1 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0070 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0071 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0072 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0073 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0074 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDF9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDF9810 A B C D E F G)
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
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0075 hApos hcq2 hcq3 hcq4 hAD hBn hEn hGn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0077 hcq2 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0078 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
      · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0079 hApos hcq2 h hAD hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hGz (by exact chamberKills3SpeedTArith0080 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0081 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0082 hcq2 hAD hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0083 hApos hcq2 hAD hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0084 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0022 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0085 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0086 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0087 hApos hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the dominated band(s). -/
theorem quarticChamberCDG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDG6810 A B C D E F G)
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
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0088 hcq3 hcq0 hBn hEn hFn hcq1 hzero)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz hFz (by exact chamberKills3SpeedTArith0089 hcq3 hcq1) (by exact chamberKills3SpeedTArith0001 hcq3) (by exact chamberKills3SpeedTArith0002 hcq3) (Or.inr (by exact chamberKills3SpeedTArith0090 hApos hcq0 hcq3 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0091 hApos hcq0 hcq3 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0092 hApos hcq0 hcq3 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0093 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0094 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0095 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0096 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CEG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the dominated band(s). -/
theorem quarticChamberCEG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG6810 A B C D E F G)
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
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0097 hcq3 hcq1 hBn hDn hFn hzero)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hFz (by exact chamberKills3SpeedTArith0001 hcq3) (by exact chamberKills3SpeedTArith0002 hcq3) (by exact chamberKills3SpeedTArith0098 hcq3 hcq0 hcq2) (Or.inr (by exact chamberKills3SpeedTArith0099 hApos hcq3 hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0100 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0101 hApos hcq0 hcq2))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CFG` / `CF·CG·FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCFG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0102 hcq1 hcq4 hBn hDn hEn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0103 hcq4 h)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hDn)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0104 h hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0105 h hcq1 hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0106 hcq1 h hcq4)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0107 hApos hcq1 h)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hDn)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0035 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0108 hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0109 hApos h hcq1)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0110 hApos hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0111 hApos hcq1 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0029 hApos hcq1))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `CFG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCFG9810 A B C D E F G)
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
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0112 hcq4 hcq0 hBn hDn hEn hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0113 hcq4 h hcq1)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hDn)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0114 h hcq0 hcq4 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0115 h hcq0 hcq4 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0116 hcq0 hcq4 h)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0117 hcq4 h hcq1)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hDn)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0118 h hcq0 hcq4 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0119 h hcq0 hcq4 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0120 hApos hcq0 h hcq1)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hEz (by exact chamberKills3SpeedTArith0001 hcq4) (by exact chamberKills3SpeedTArith0121 hcq1) (by exact chamberKills3SpeedTArith0002 hcq4) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0003 hApos hcq4 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0122 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0123 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0004 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0124 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DEF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDEF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0125 hApos hcq2 hAD hBn hCn hGn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq2 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0127 hcq2 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0128 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
      · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0129 hApos hcq2 h hcq0)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0018 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0019 hApos h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0130 hApos hcq2 h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0020 hApos h)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0131 hApos h hcq2 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_DEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hGz (by exact chamberKills3SpeedTArith0132 hcq2 hAD hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0133 hApos hcq2 hcq0)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0022 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0023 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0024 hApos hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DEG` / `DD·DG·GG` dies on the `π` face `2 * G.natDegree`, using the dominated band(s). -/
theorem quarticChamberDEG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0134 hApos hcq2 hcq0 hAD hBn hCn hFn hzero)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_DEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hFz (by exact chamberKills3SpeedTArith0135 hcq0 hAD hcq4) (Or.inr (by exact chamberKills3SpeedTArith0136 hApos hcq0 hAD hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0137 hApos hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0138 hApos hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0139 hApos hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0028 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0140 hApos hcq0 hcq4))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DEG` / `EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDEG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0141 hApos hAE hAD hBn hCn hFn hcq2 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0142 hAE h hcq2 hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0143 h hAE hcq2 hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hFn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0144 h hAE hcq2 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0145 hAE h hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0146 hAE h hcq2 hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0147 hApos h hcq2 hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hFn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0148 hApos h hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0149 hApos h hcq2 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_DEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hFz hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0150 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0151 hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0152 hApos hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0153 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0154 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0155 hApos hcq2 hcq0))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `DFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0156 hApos hcq2 hAD hBn hCn hEn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq2 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0158 hcq2 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
    · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
    · exact Or.inr (by exact chamberKills3SpeedTArith0159 h hcq2 hAD hcq0)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0018 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hCn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0019 hApos h hcq0)
    · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hEn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0020 hApos h)
    · exact Or.inr (by exact chamberKills3SpeedTArith0160 hApos h hcq2 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_DFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hEz (by exact chamberKills3SpeedTArith0161 hcq2 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0021 hApos hcq0)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0022 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0023 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0162 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0024 hApos hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DFG` / `DD·DG·GG` dies on the `π` face `2 * G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDFG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDFG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0163 hApos hcq0 hAD hBn hCn hEn hcq2 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0164 hcq0 hAD h hcq2)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0165 h hcq0 hAD hcq2)
      · exact Or.inr (by exact chamberKills3SpeedTArith0166 h hAD hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0167 hApos hcq0 h hAD hcq2)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0168 hApos hcq0 h hcq2)
    · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0169 h hcq0 hAD hcq2)
    · exact Or.inr (by exact chamberKills3SpeedTArith0170 hApos h hcq0 hcq2)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_DFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hEz (by exact chamberKills3SpeedTArith0171 hcq0 hcq2) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0172 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0173 hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0028 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0174 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0029 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0175 hApos hcq0 hcq2))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `EFG` / `EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberEFG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0176 hApos hAE hBn hCn hDn hcq2 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0031 h hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0032 h hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0177 h hAE hcq0 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0033 h hAE)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
    · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hDn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0034 hApos h hcq0)
    · exact Or.inr (by exact chamberKills3SpeedTArith0035 hApos h)
    · exact Or.inr (by exact chamberKills3SpeedTArith0178 h hAE hcq0 hcq2)
  have hzdelta : delta = 0 ∨ (A.natDegree + F.natDegree < 2 * F.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0018 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hCn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hDn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0036 hApos h hcq0)
    · exact Or.inr (by exact chamberKills3SpeedTArith0037 hApos h)
    · exact Or.inr (by exact chamberKills3SpeedTArith0179 h hAE hcq0 hcq2)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_EFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz (by exact chamberKills3SpeedTArith0180 hcq2 hcq0) hzl hzbeta hzdelta (Or.inr (by exact chamberKills3SpeedTArith0181 hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0038 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0039 hApos hcq0))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `EFG` / `EE·EG·GG` dies on the `π` face `2 * G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberEFG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberEFG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0182 hApos hcq2 hAE hBn hCn hDn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0183 h hcq2 hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0184 h hcq2 hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0185 h hcq2 hAE)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0186 hAE h hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0187 hApos hcq2 h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0188 h hcq2 hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0189 hApos h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0190 hApos hcq2 h hcq0)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0018 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hCn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hDn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0191 hApos hcq2 h hcq0)
    · exact Or.inr (by exact chamberKills3SpeedTArith0192 hApos hcq2 h hcq0)
    · exact Or.inr (by exact chamberKills3SpeedTArith0193 hApos h hcq2 hcq0)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_EFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz (by exact chamberKills3SpeedTArith0194 hcq2 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0041 hApos hcq0)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0195 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0042 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0196 hApos hcq2 hcq0))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `CF·DD·DF·FF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDF19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0197 hcq0 hcq9 hcq7 hEn hGn hcq3 hcq1 hcq4 hcq5 hzero)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0198 hcq0 hcq9 h hcq1 hGn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0199 hcq0 hcq9 h hcq1 hEn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0200 h hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0201 hcq0 h hcq1 hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0202 hcq0 hAE hcq9 h hcq1 hEn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0203 h hcq1 hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0204 h hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0205 hcq0 h hcq3 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0206 hcq0 h hcq1 hcq3 hcq10)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0207 hcq0 hcq9 h hcq1 hGn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0208 hcq0 hcq9 h hcq1 hEn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0209 h hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0210 hcq0 h hcq1 hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0211 hcq0 hAE hcq9 h hcq1 hEn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0212 h hcq1 hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0213 h hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0214 hcq0 h hcq3 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0215 hcq0 h hcq1 hcq3 hcq10)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0216 hcq0 h hcq9 hcq1 hGn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0217 hcq0 h hcq9 hcq1 hEn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0218 h hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0219 hcq0 h hcq1 hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0220 hcq0 hAE h hcq9 hcq1 hEn hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0221 h hcq1 hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0222 h hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0223 hcq0 h hcq3 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0224 hcq0 hAE h hcq1 hcq3 hcq10 hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0225 hcq0 h hcq1 hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0226 hcq0 h hcq1 hcq3 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0227 hcq0 h hcq1 hcq3 hcq10)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by exact chamberKills3SpeedTArith0228 hcq3 hcq1 hcq10) (by exact chamberKills3SpeedTArith0229 hcq10 hcq3) (by exact chamberKills3SpeedTArith0230 hcq10 hcq3 hcq1) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0231 hApos hcq0 hcq10 hcq3 hcq1)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0232 hcq10 hcq3)) (Or.inr (by exact chamberKills3SpeedTArith0233 hcq0 hcq1 hcq3 hcq10)) (Or.inr (by exact chamberKills3SpeedTArith0234 hApos hcq0 hcq3 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0235 hcq1 hcq3 hcq10))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  exact Nat.ne_of_gt hdpos hkap

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBCDF25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0236 hApos hAB hcq6 hcq10 hAD hEn hGn hcq4 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq3 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0237 hcq3 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hGz (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0238 hcq3 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0239 hcq3 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0240 hcq3 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0080 hcq3 hAD hcq0) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0241 hcq3 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0081 hcq3 hAD hcq0) (by exact chamberKills3SpeedTArith0082 hcq3 hAD hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0242 hApos hcq3 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0243 hApos hcq3 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0244 hApos hcq3 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0245 hApos hcq3 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0246 hApos hcq3 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0247 hApos hcq3 hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0248 hApos hcq3 hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBDEF18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0249 hApos hcq3 hAB hcq7 hAD hCn hGn hcq6 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq3 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0250 hcq3 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0251 hcq3 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0252 hcq3 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0132 hcq3 hAD hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0253 hApos hcq3 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0254 hApos hcq3 hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0255 hApos hcq3 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0053 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0256 hApos hcq3 hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0055 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0056 hApos hcq0 hcq2))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `DD·DF·DG·FF·FG·GG` dies on the `ν` face `D.natDegree + G.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDFG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0257 hApos hcq1 hAB hcq8 hAD hcq5 hCn hEn hcq7 hcq0 hzero)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 4 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0258 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0259 hApos hcq1 hAD h hcq0 hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0260 hApos hcq1 hAD h hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0261 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0262 hcq1 hAD h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0263 hApos hcq1 hAB hcq8 h hCn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0264 hcq1 hAD h hcq0 hcq5)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0265 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0266 hApos hcq1 h hAD hcq0 hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0267 hApos hcq1 h hAD hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0268 hcq1 hAD hcq0 h hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0269 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0270 hApos hcq1 hAB h hcq8 hCn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0271 h hAD hcq0 hcq5)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0272 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0273 hcq1 h hcq0 hCn hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0274 hApos hcq1 h hAD hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0275 h hcq1 hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0276 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0277 hApos hcq1 hAB h hcq8 hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0278 hcq1 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0279 hAC hcq1 h hAD hcq0 hCn hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0280 hApos hcq1 h hcq0 hcq5)
  have hrest : (nuQuarticChamberRest1000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    nuQuarticChamberRest1000810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by exact chamberKills3SpeedTArith0281 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0282 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0283 hcq0 hcq5) (by exact chamberKills3SpeedTArith0284 hcq1 hAD hcq5 hcq0) (by exact chamberKills3SpeedTArith0285 hcq1 hAD hcq5 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0286 hApos hcq1 hAD hcq5 hcq0)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0287 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0288 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0289 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0290 hApos hcq1 hcq0 hcq5))
  have hlead : (nuQuarticChamberFace1000810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    nuQuarticChamberFace1000810_natDegree A B C D E F G hDne hGne
  rw [degreeZeroNuQuartic810_eq_face1000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hnu
  exact Nat.ne_of_gt hdpos hnu

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBDFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0291 hApos hcq4 hcq8 hAD hCn hEn hcq7 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq4 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0292 hcq4 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0293 hcq4 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0294 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0161 hcq4 hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0050 hApos hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0051 hApos hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0052 hApos hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0053 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0054 hApos hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0295 hApos hcq4 hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0056 hApos hcq0 hcq2))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDEF8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0296 hcq0 hcq6 hBn hcq3 hGn hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0058 h hcq1 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0059 h hcq1 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0297 h hcq0 hcq1 hcq7 hcq3)
      · exact Or.inr (by exact chamberKills3SpeedTArith0060 h hcq0 hcq1 hcq7)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0298 hcq0 h hcq1 hcq7 hcq3)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0062 h hcq1 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0063 h hcq1 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0299 hcq0 h hcq1 hcq7 hcq3)
      · exact Or.inr (by exact chamberKills3SpeedTArith0064 h hcq0 hcq1 hcq7)
      · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0300 hcq0 h hcq1 hcq7 hcq3)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by exact chamberKills3SpeedTArith0066 hcq0 hcq1 hcq7) (by exact chamberKills3SpeedTArith0067 hcq7 hcq1) (by exact chamberKills3SpeedTArith0068 hcq7) (by exact chamberKills3SpeedTArith0301 hcq0 hcq7 hcq1 hcq3) (by exact chamberKills3SpeedTArith0302 hcq3 hcq7) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0303 hApos hcq0 hcq1 hcq3 hcq7)) (Or.inr (by exact chamberKills3SpeedTArith0304 hApos hcq0 hcq1 hcq3)) (Or.inr (by exact chamberKills3SpeedTArith0305 hApos hcq0 hcq1 hcq3)) (Or.inr (by exact chamberKills3SpeedTArith0306 hApos hcq0 hcq1 hcq3)) (Or.inr (by exact chamberKills3SpeedTArith0073 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0074 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDEF18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0307 hApos hcq2 hcq3 hcq6 hcq7 hAD hBn hGn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq3 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0308 hcq2 hcq3 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0078 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0128 hcq3 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
      · exact absurd h (by exact chamberKills3SpeedTArith0017 hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0309 hApos hcq2 hcq3 h hAD hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by exact chamberKills3SpeedTArith0080 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0081 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0082 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0310 hcq2 hcq3 hAD hcq0) (by exact chamberKills3SpeedTArith0132 hcq3 hAD hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0311 hApos hcq2 hcq3 hAD hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0312 hApos hcq2 hcq3 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0313 hApos hcq2 hcq3 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0085 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0086 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0087 hApos hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the dominated band(s). -/
theorem quarticChamberCDEG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0314 hcq6 hcq4 hcq0 hBn hFn hcq1 hzero)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by exact chamberKills3SpeedTArith0089 hcq6 hcq1) (by exact chamberKills3SpeedTArith0001 hcq6) (by exact chamberKills3SpeedTArith0002 hcq6) (by exact chamberKills3SpeedTArith0098 hcq6 hcq0 hcq5) (by exact chamberKills3SpeedTArith0315 hcq6 hcq5 hcq1) (Or.inr (by exact chamberKills3SpeedTArith0316 hApos hcq0 hcq6 hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0317 hApos hcq0 hcq6 hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0318 hApos hcq0 hcq6 hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0319 hApos hcq0 hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0320 hApos hcq0 hcq5 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0095 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0101 hApos hcq0 hcq5))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CF·CG·FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0321 hcq1 hcq7 hBn hEn hcq0 hcq4 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0103 hcq7 h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0322 hcq7 h hcq0 hcq6)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0104 h hcq1 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0105 h hcq1 hcq7 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0323 hcq1 h hcq7 hcq0 hcq6)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0107 hApos hcq1 h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0324 hcq7 h hcq0 hcq6)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0035 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0108 hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0325 hApos h hcq1 hcq0 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by exact chamberKills3SpeedTArith0326 hcq1 hcq0 hcq6) (by exact chamberKills3SpeedTArith0327 hcq1 hcq7 hcq6 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0328 hApos hcq1 hcq6 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0329 hApos hcq1 hcq0 hcq6)) (Or.inr (by exact chamberKills3SpeedTArith0330 hApos hcq1 hcq6)) (Or.inr (by exact chamberKills3SpeedTArith0331 hApos hcq1 hcq0 hcq6)) (Or.inr (by exact chamberKills3SpeedTArith0332 hApos hcq1 hcq6 hcq0))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0333 hcq0 hcq3 hcq7 hBn hEn hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0058 h hcq1 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0059 h hcq1 hcq8)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0060 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0334 h hcq0 hcq1 hcq8 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0335 hcq0 h hcq1 hcq8 hcq4)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0062 h hcq1 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0063 h hcq1 hcq8)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0064 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0336 h hcq0 hcq1 hcq8 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0065 hcq0 h hcq1 hcq8)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by exact chamberKills3SpeedTArith0066 hcq0 hcq1 hcq8) (by exact chamberKills3SpeedTArith0067 hcq8 hcq1) (by exact chamberKills3SpeedTArith0337 hcq8 hcq1 hcq4) (by exact chamberKills3SpeedTArith0068 hcq8) (by exact chamberKills3SpeedTArith0338 hcq1 hcq4) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0069 hApos hcq0 hcq1 hcq8)) (Or.inr (by exact chamberKills3SpeedTArith0070 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0071 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0072 hApos hcq0 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0339 hApos hcq0 hcq1 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0074 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0340 hcq7 hcq0 hBn hEn hcq2 hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0113 hcq7 h hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0341 hcq0 hcq7 h hcq1 hcq2)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0114 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0115 h hcq0 hcq7 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0342 hApos hcq0 hcq7 h hcq2)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0117 hcq7 h hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0343 hcq0 hcq7 h hcq1 hcq2)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0118 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0119 h hcq0 hcq7 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0344 hApos hcq0 hcq7 h hcq1 hcq2)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by exact chamberKills3SpeedTArith0089 hcq7 hcq2) (by exact chamberKills3SpeedTArith0001 hcq7) (by exact chamberKills3SpeedTArith0121 hcq1) (by exact chamberKills3SpeedTArith0002 hcq7) (by exact chamberKills3SpeedTArith0345 hcq7 hcq0 hcq2 hcq1) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0346 hApos hcq0 hcq7 hcq2 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0347 hApos hcq0 hcq1 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0094 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0348 hApos hcq0 hcq1 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0096 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0124 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0349 hApos hcq2 hcq4 hcq7 hcq8 hAD hBn hEn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq4 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0350 hcq2 hcq4 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0078 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0159 h hcq4 hAD hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0079 hApos hcq2 h hAD hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by exact chamberKills3SpeedTArith0080 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0081 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0351 hcq2 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0082 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0161 hcq4 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0083 hApos hcq2 hAD hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0084 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0022 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0085 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0352 hApos hcq2 hcq4 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0087 hApos hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CF·CG·FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCEFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0353 hcq1 hcq7 hcq4 hBn hDn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0103 hcq7 h)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0354 h hcq7 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0104 h hcq1 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0105 h hcq1 hcq7 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0355 hcq1 h hcq7 hcq5)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0107 hApos hcq1 h)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0356 hcq7 h hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0035 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0108 hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0109 hApos h hcq1)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by exact chamberKills3SpeedTArith0357 hcq1 hcq7 hcq5) (by exact chamberKills3SpeedTArith0358 hcq1 hcq5 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0359 hApos hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0360 hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0361 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0362 hApos hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0175 hApos hcq1 hcq5))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `CEFG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCEFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0363 hcq7 hcq2 hcq0 hBn hDn hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0113 hcq7 h hcq1)
      · exact absurd h (by exact chamberKills3SpeedTArith0015 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0364 h hcq7 hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0114 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0115 h hcq0 hcq7 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0365 hcq0 hcq7 h hcq4)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0117 hcq7 h hcq1)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hDn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0366 hcq7 h hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0118 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0119 h hcq0 hcq7 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0367 hApos hcq0 h hcq1 hcq4)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by exact chamberKills3SpeedTArith0001 hcq7) (by exact chamberKills3SpeedTArith0121 hcq1) (by exact chamberKills3SpeedTArith0002 hcq7) (by exact chamberKills3SpeedTArith0098 hcq7 hcq0 hcq4) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0099 hApos hcq7 hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0368 hApos hcq0 hcq1 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0100 hApos hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0369 hApos hcq0 hcq1 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0101 hApos hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0124 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0370 hApos hcq2 hcq3 hAD hBn hCn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq2 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq3 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0371 hcq2 hcq3 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0128 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0159 h hcq3 hAD hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0129 hApos hcq2 h hcq0)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0018 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0019 hApos h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0130 hApos hcq2 h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0020 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0160 hApos h hcq3 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0131 hApos h hcq2 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by exact chamberKills3SpeedTArith0132 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0161 hcq3 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0133 hApos hcq2 hcq0)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0022 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0023 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0162 hApos hcq3 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0024 hApos hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `DD·DG·GG` dies on the `π` face `2 * G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDEFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0372 hApos hcq2 hcq0 hAD hBn hCn hcq3 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0164 hcq0 hAD h hcq3)
      · exact Or.inr (by exact chamberKills3SpeedTArith0373 h hcq0 hAD hcq3 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0165 h hcq0 hAD hcq3)
      · exact Or.inr (by exact chamberKills3SpeedTArith0166 h hAD hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0374 hApos hcq0 h hAD hcq3 hcq6)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0168 hApos hcq0 h hcq3)
      · exact Or.inr (by exact chamberKills3SpeedTArith0375 hcq0 hAD h hcq3 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0169 h hcq0 hAD hcq3)
      · exact Or.inr (by exact chamberKills3SpeedTArith0170 hApos h hcq0 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0376 hApos hcq0 h hcq3 hcq6)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by exact chamberKills3SpeedTArith0171 hcq0 hcq3) (by exact chamberKills3SpeedTArith0135 hcq0 hAD hcq6) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0377 hApos hcq0 hcq3 hcq6)) (Or.inr (by exact chamberKills3SpeedTArith0378 hApos hcq0 hcq3 hcq6)) (Or.inr (by exact chamberKills3SpeedTArith0028 hApos hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0379 hApos hcq0 hcq3 hcq6)) (Or.inr (by exact chamberKills3SpeedTArith0140 hApos hcq0 hcq6)) (Or.inr (by exact chamberKills3SpeedTArith0380 hApos hcq0 hcq3 hcq6))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDEFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0381 hApos hcq5 hAE hAD hBn hCn hcq6 hcq2 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0382 hAE h hcq0 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0031 h hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0032 h hAE hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0177 h hAE hcq0 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0383 h hAE hcq0 hcq4 hcq6)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0384 hAE h hcq0 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0034 hApos h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0035 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0178 h hAE hcq0 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0385 hApos h hcq0 hcq4)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by exact chamberKills3SpeedTArith0386 hcq0 hcq4) (by exact chamberKills3SpeedTArith0180 hcq6 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0387 hApos hcq4 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0388 hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0389 hApos hcq6 hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0390 hApos hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0391 hApos hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0392 hApos hcq4 hcq0))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberDEFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0393 hApos hcq6 hAE hAD hBn hCn hcq2 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0394 hAE h hcq2 hcq0 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0395 h hcq6 hAE hcq2 hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0396 h hcq6 hAE hcq2 hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0397 h hcq6 hAE hcq2 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0398 hAE h hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
    · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hCn)
    · exact Or.inr (by exact chamberKills3SpeedTArith0399 hAE h hcq2 hcq0 hcq4)
    · exact Or.inr (by exact chamberKills3SpeedTArith0400 hApos hcq6 h hcq2 hcq0)
    · exact Or.inr (by exact chamberKills3SpeedTArith0401 h hcq6 hAE hcq0 hcq4)
    · exact Or.inr (by exact chamberKills3SpeedTArith0402 hApos h hcq6 hcq2 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by exact chamberKills3SpeedTArith0403 hcq0 hcq4) (by exact chamberKills3SpeedTArith0404 hcq6 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0150 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0405 hcq2 hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0152 hApos hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0406 hApos hcq2 hcq0 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0154 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0155 hApos hcq2 hcq0))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·DD·DF·FF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEF34810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF34810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0407 hcq0 hcq14 hcq11 hcq4 hGn hcq3 hcq1 hcq7 hcq8 hzero)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0198 hcq0 hcq14 h hcq1 hGn hcq11)
      · exact Or.inr (by exact chamberKills3SpeedTArith0408 hcq0 h hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0200 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0201 hcq0 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0409 hcq0 h hcq3 hcq15 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0203 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0204 h hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0205 hcq0 h hcq3 hcq15)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0410 hcq0 h hcq1 hcq3 hcq15 hcq4)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0207 hcq0 hcq14 h hcq1 hGn hcq11)
      · exact Or.inr (by exact chamberKills3SpeedTArith0411 hcq0 h hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0209 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0210 hcq0 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0412 hcq0 h hcq3 hcq15 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0212 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0213 h hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0214 hcq0 h hcq3 hcq15)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0413 hcq0 h hcq1 hcq3 hcq15 hcq4)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0216 hcq0 h hcq14 hcq1 hGn hcq11)
      · exact Or.inr (by exact chamberKills3SpeedTArith0414 hcq0 h hcq1 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0218 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0219 hcq0 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0415 hcq0 h hcq3 hcq15 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0221 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0222 h hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0223 hcq0 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0416 hcq0 h hcq1 hcq3 hcq15 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0225 hcq0 h hcq1 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0226 hcq0 h hcq1 hcq3 hcq15)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0417 hcq0 h hcq1 hcq3 hcq15 hcq4)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by exact chamberKills3SpeedTArith0228 hcq3 hcq1 hcq15) (by exact chamberKills3SpeedTArith0229 hcq15 hcq3) (by exact chamberKills3SpeedTArith0230 hcq15 hcq3 hcq1) (by exact chamberKills3SpeedTArith0418 hcq4) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0231 hApos hcq0 hcq15 hcq3 hcq1)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0232 hcq15 hcq3)) (Or.inr (by exact chamberKills3SpeedTArith0233 hcq0 hcq1 hcq3 hcq15)) (Or.inr (by exact chamberKills3SpeedTArith0234 hApos hcq0 hcq3 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0235 hcq1 hcq3 hcq15))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  exact Nat.ne_of_gt hdpos hkap

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBCDEF48810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF48810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0419 hApos hcq4 hAB hcq9 hcq15 hAD hGn hcq7 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq3 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq4 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0011 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0420 hcq3 hcq4 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0238 hcq3 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0239 hcq3 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0240 hcq3 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0251 hcq4 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0080 hcq3 hAD hcq0) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0421 hcq3 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0241 hcq3 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0081 hcq3 hAD hcq0) (by exact chamberKills3SpeedTArith0252 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0082 hcq3 hAD hcq0) (by exact chamberKills3SpeedTArith0310 hcq3 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0132 hcq4 hAD hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0422 hApos hcq3 hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0423 hApos hcq3 hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0424 hApos hcq3 hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0425 hApos hcq3 hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0426 hApos hcq3 hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0247 hApos hcq3 hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0248 hApos hcq3 hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `CF·DD·DF·FF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDFG49810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG49810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0427 hcq0 hcq14 hcq12 hcq4 hEn hcq3 hcq1 hcq9 hcq10 hzero)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0428 h hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0199 hcq0 hcq14 h hcq1 hEn hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0200 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0201 hcq0 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0202 hcq0 hAE hcq14 h hcq1 hEn hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0203 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0204 h hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0205 hcq0 h hcq3 hcq15)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0429 hcq0 h hcq1 hcq3 hcq15 hcq6)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0430 h hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0208 hcq0 hcq14 h hcq1 hEn hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0209 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0210 hcq0 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0211 hcq0 hAE hcq14 h hcq1 hEn hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0212 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0213 h hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0214 hcq0 h hcq3 hcq15)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0431 hcq0 h hcq1 hcq3 hcq15 hcq6)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0432 h hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0217 hcq0 h hcq14 hcq1 hEn hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0218 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0219 hcq0 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0433 hcq0 h hcq14 hcq1 hcq6 hcq12 hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0221 h hcq1 hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0222 h hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0223 hcq0 h hcq3 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0224 hcq0 hAE h hcq1 hcq3 hcq15 hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0225 hcq0 h hcq1 hcq15)
      · exact Or.inr (by exact chamberKills3SpeedTArith0226 hcq0 h hcq1 hcq3 hcq15)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0227 hcq0 h hcq1 hcq3 hcq15)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by exact chamberKills3SpeedTArith0228 hcq3 hcq1 hcq15) (by exact chamberKills3SpeedTArith0229 hcq15 hcq3) (by exact chamberKills3SpeedTArith0230 hcq15 hcq3 hcq1) (by exact chamberKills3SpeedTArith0434 hcq3 hcq1 hcq6) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0231 hApos hcq0 hcq15 hcq3 hcq1)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0232 hcq15 hcq3)) (Or.inr (by exact chamberKills3SpeedTArith0233 hcq0 hcq1 hcq3 hcq15)) (Or.inr (by exact chamberKills3SpeedTArith0435 hcq0 hcq15 hcq3 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0235 hcq1 hcq3 hcq15))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  exact Nat.ne_of_gt hdpos hkap

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `DD·DF·DG·FF·FG·GG` dies on the `ν` face `D.natDegree + G.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDFG61810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG61810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0436 hApos hcq14 hcq1 hAB hcq11 hcq15 hAD hcq5 hEn hcq9 hcq0 hzero)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 4 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 3 * C.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0258 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0437 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0260 hApos hcq1 hAD h hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0261 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0262 hcq1 hAD h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0438 hcq1 hAD h hcq0 hcq5 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0439 hcq1 hAD h hcq0 hcq8 hcq5)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0265 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0440 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0267 hApos hcq1 h hAD hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0268 hcq1 hAD hcq0 h hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0269 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0441 hcq1 h hAD hcq0 hcq5 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0442 hcq1 h hAD hcq0 hcq8 hcq5)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * C.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0272 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0443 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0274 hApos hcq1 h hAD hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0275 h hcq1 hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0276 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0444 hcq1 h hAD hcq0 hcq5 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0278 hcq1 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0445 hcq1 h hAD hcq0 hcq5 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0446 hApos hcq1 h hcq0 hcq8 hcq5)
  have hrest : (nuQuarticChamberRest1000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    nuQuarticChamberRest1000810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by exact chamberKills3SpeedTArith0281 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0282 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0447 hcq1 hAD hcq0 hcq5 hcq8) (by exact chamberKills3SpeedTArith0448 hcq1 hAD hcq5 hcq8 hcq0) (by exact chamberKills3SpeedTArith0283 hcq0 hcq5) (by exact chamberKills3SpeedTArith0449 hcq1 hcq0 hcq8) (by exact chamberKills3SpeedTArith0284 hcq1 hAD hcq5 hcq0) (by exact chamberKills3SpeedTArith0285 hcq1 hAD hcq5 hcq0) (by exact chamberKills3SpeedTArith0450 hcq1 hAD hcq8) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0451 hApos hcq1 hAD hcq0 hcq5 hcq8)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0452 hApos hcq1 hcq0 hcq5 hcq8)) (Or.inr (by exact chamberKills3SpeedTArith0288 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0289 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0453 hApos hcq1 hcq0 hcq8 hcq5))
  have hlead : (nuQuarticChamberFace1000810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    nuQuarticChamberFace1000810_natDegree A B C D E F G hDne hGne
  rw [degreeZeroNuQuartic810_eq_face1000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hnu
  exact Nat.ne_of_gt hdpos hnu

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBCDFG62810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG62810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0454 hApos hcq6 hcq11 hcq15 hAD hEn hcq9 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq4 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact absurd h (by exact chamberKills3SpeedTArith0009 hApos hEn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq6 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0455 hcq4 hcq6 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0238 hcq4 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0239 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0293 hcq6 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0240 hcq4 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0080 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0241 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0081 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0294 hcq6 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0351 hcq4 hcq6 hAD hcq0) (by exact chamberKills3SpeedTArith0082 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0161 hcq6 hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0242 hApos hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0243 hApos hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0244 hApos hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0245 hApos hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0246 hApos hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0456 hApos hcq4 hcq6 hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0248 hApos hcq4 hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD·DF·DG·FF·FG·GG` dies on the `ν` face `D.natDegree + G.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBDEFG44810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG44810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0457 hApos hcq7 hcq1 hAB hcq12 hAD hcq5 hCn hcq11 hcq0 hzero)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 4 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * E.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0258 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0259 hApos hcq1 hAD h hcq0 hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0458 hcq1 h hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0261 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0262 hcq1 hAD h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0263 hApos hcq1 hAB hcq12 h hCn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0459 hcq1 hAD h hcq0 hcq10 hcq5)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0265 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0266 hApos hcq1 h hAD hcq0 hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0460 hcq1 h hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0268 hcq1 hAD hcq0 h hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0269 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0270 hApos hcq1 hAB h hcq12 hCn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0461 hcq1 h hAD hcq0 hcq5 hcq10)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0272 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0273 hcq1 h hcq0 hCn hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0462 hcq1 h hcq10)
      · exact Or.inr (by exact chamberKills3SpeedTArith0275 h hcq1 hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0276 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0277 hApos hcq1 hAB h hcq12 hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0278 hcq1 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0279 hAC hcq1 h hAD hcq0 hCn hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0280 hApos hcq1 h hcq0 hcq5)
  have hrest : (nuQuarticChamberRest1000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    nuQuarticChamberRest1000810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by exact chamberKills3SpeedTArith0281 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0282 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0283 hcq0 hcq5) (by exact chamberKills3SpeedTArith0463 hcq1 hcq10) (by exact chamberKills3SpeedTArith0284 hcq1 hAD hcq5 hcq0) (by exact chamberKills3SpeedTArith0285 hcq1 hAD hcq5 hcq0) (by exact chamberKills3SpeedTArith0464 hcq1 hcq10 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0465 hApos hcq1 hAD hcq5 hcq0 hcq10)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0287 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0466 hApos hcq1 hcq0 hcq5 hcq10)) (Or.inr (by exact chamberKills3SpeedTArith0289 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0290 hApos hcq1 hcq0 hcq5))
  have hlead : (nuQuarticChamberFace1000810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    nuQuarticChamberFace1000810_natDegree A B C D E F G hDne hGne
  rw [degreeZeroNuQuartic810_eq_face1000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hnu
  exact Nat.ne_of_gt hdpos hnu

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBDEFG45810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG45810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0467 hApos hcq4 hcq5 hcq12 hAD hCn hcq11 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact absurd h (by exact chamberKills3SpeedTArith0007 hApos hCn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq4 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq5 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0468 hcq4 hcq5 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0293 hcq5 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0251 hcq4 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0294 hcq5 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0252 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0132 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0161 hcq5 hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0253 hApos hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0254 hApos hcq4 hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0255 hApos hcq4 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0053 hApos hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0256 hApos hcq4 hAD hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0295 hApos hcq5 hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0056 hApos hcq0 hcq2))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·CG·FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDEFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0469 hcq1 hcq11 hcq8 hBn hcq0 hcq4 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0103 hcq11 h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0322 hcq11 h hcq0 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0354 h hcq11 hcq9)
      · exact Or.inr (by exact chamberKills3SpeedTArith0104 h hcq1 hcq11)
      · exact Or.inr (by exact chamberKills3SpeedTArith0105 h hcq1 hcq11 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0470 hcq1 h hcq11 hcq0 hcq7 hcq9)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0107 hApos hcq1 h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0324 hcq11 h hcq0 hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0356 hcq11 h hcq9)
      · exact Or.inr (by exact chamberKills3SpeedTArith0035 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0108 hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0471 hApos h hcq1 hcq0 hcq7 hcq9)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by exact chamberKills3SpeedTArith0326 hcq1 hcq0 hcq7) (by exact chamberKills3SpeedTArith0357 hcq1 hcq11 hcq9) (by exact chamberKills3SpeedTArith0327 hcq1 hcq11 hcq7 hcq0) (by exact chamberKills3SpeedTArith0358 hcq1 hcq9 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0472 hApos hcq1 hcq9 hcq7 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0329 hApos hcq1 hcq0 hcq7)) (Or.inr (by exact chamberKills3SpeedTArith0330 hApos hcq1 hcq7)) (Or.inr (by exact chamberKills3SpeedTArith0331 hApos hcq1 hcq0 hcq7)) (Or.inr (by exact chamberKills3SpeedTArith0473 hApos hcq1 hcq9 hcq0 hcq7)) (Or.inr (by exact chamberKills3SpeedTArith0332 hApos hcq1 hcq7 hcq0))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact Nat.ne_of_gt hdpos hxi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDEFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0474 hcq0 hcq3 hcq11 hBn hcq4 hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0058 h hcq1 hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0059 h hcq1 hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0297 h hcq0 hcq1 hcq12 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0060 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0334 h hcq0 hcq1 hcq12 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0475 hcq0 h hcq1 hcq12 hcq4 hcq5)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0062 h hcq1 hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0063 h hcq1 hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0299 hcq0 h hcq1 hcq12 hcq4)
      · exact Or.inr (by exact chamberKills3SpeedTArith0064 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0336 h hcq0 hcq1 hcq12 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0300 hcq0 h hcq1 hcq12 hcq4)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by exact chamberKills3SpeedTArith0066 hcq0 hcq1 hcq12) (by exact chamberKills3SpeedTArith0067 hcq12 hcq1) (by exact chamberKills3SpeedTArith0337 hcq12 hcq1 hcq5) (by exact chamberKills3SpeedTArith0068 hcq12) (by exact chamberKills3SpeedTArith0301 hcq0 hcq12 hcq1 hcq4) (by exact chamberKills3SpeedTArith0302 hcq4 hcq12) (by exact chamberKills3SpeedTArith0338 hcq1 hcq5) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0303 hApos hcq0 hcq1 hcq4 hcq12)) (Or.inr (by exact chamberKills3SpeedTArith0304 hApos hcq0 hcq1 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0305 hApos hcq0 hcq1 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0306 hApos hcq0 hcq1 hcq4)) (Or.inr (by exact chamberKills3SpeedTArith0339 hApos hcq0 hcq1 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0074 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CG·GG` dies on the `π` face `2 * G.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDEFG36810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG36810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0476 hcq11 hcq6 hcq0 hBn hcq2 hcq1 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0113 hcq11 h hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0341 hcq0 hcq11 h hcq1 hcq2)
      · exact Or.inr (by exact chamberKills3SpeedTArith0364 h hcq11 hcq1 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0114 h hcq0 hcq11 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0115 h hcq0 hcq11 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0477 hApos hcq0 hcq11 h hcq2 hcq8)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0117 hcq11 h hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0343 hcq0 hcq11 h hcq1 hcq2)
      · exact Or.inr (by exact chamberKills3SpeedTArith0366 hcq11 h hcq1 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0118 h hcq0 hcq11 hcq1)
      · exact Or.inr (by exact chamberKills3SpeedTArith0119 h hcq0 hcq11 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0478 hApos hcq0 hcq11 h hcq1 hcq2 hcq8)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by exact chamberKills3SpeedTArith0089 hcq11 hcq2) (by exact chamberKills3SpeedTArith0001 hcq11) (by exact chamberKills3SpeedTArith0121 hcq1) (by exact chamberKills3SpeedTArith0002 hcq11) (by exact chamberKills3SpeedTArith0345 hcq11 hcq0 hcq2 hcq1) (by exact chamberKills3SpeedTArith0098 hcq11 hcq0 hcq8) (by exact chamberKills3SpeedTArith0315 hcq11 hcq8 hcq2) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0479 hApos hcq0 hcq11 hcq2 hcq1 hcq8)) (Or.inr (by exact chamberKills3SpeedTArith0480 hApos hcq0 hcq1 hcq2 hcq8)) (Or.inr (by exact chamberKills3SpeedTArith0320 hApos hcq0 hcq8 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0481 hApos hcq0 hcq1 hcq2 hcq8)) (Or.inr (by exact chamberKills3SpeedTArith0101 hApos hcq0 hcq8)) (Or.inr (by exact chamberKills3SpeedTArith0124 hApos hcq0 hcq1))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberCDEFG45810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG45810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0482 hApos hcq2 hcq4 hcq5 hcq11 hcq12 hAD hBn hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0006 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq4 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq5 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0483 hcq2 hcq4 hcq5 h hAD hcq0)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact chamberKills3SpeedTArith0013 hApos hBn)
      · exact Or.inr (by exact chamberKills3SpeedTArith0078 hcq2 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0014 hApos h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0128 hcq4 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0016 hApos h)
      · exact Or.inr (by exact chamberKills3SpeedTArith0159 h hcq5 hAD hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0309 hApos hcq2 hcq4 h hAD hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by exact chamberKills3SpeedTArith0080 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0081 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0351 hcq2 hcq5 hAD hcq0) (by exact chamberKills3SpeedTArith0082 hcq2 hAD hcq0) (by exact chamberKills3SpeedTArith0310 hcq2 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0132 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0161 hcq5 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0311 hApos hcq2 hcq4 hAD hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0312 hApos hcq2 hcq4 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0313 hApos hcq2 hcq4 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0085 hApos hcq2 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0352 hApos hcq2 hcq5 hcq0)) (Or.inr (by exact chamberKills3SpeedTArith0087 hApos hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `CF·DD·DF·FF` dies on the `κ` face `C.natDegree + F.natDegree`, using the n2-cost band(s). -/
theorem quarticChamberBCDEFG94810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG94810 A B C D E F G)
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
    exact hnc (by exact chamberKills3SpeedTArith0484 hcq0 hcq20 hcq17 hcq4 hcq6 hcq3 hcq1 hcq13 hcq14 hzero)
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0428 h hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0408 hcq0 h hcq1 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0200 h hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0201 hcq0 h hcq1 hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0409 hcq0 h hcq3 hcq21 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0203 h hcq1 hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0204 h hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0205 hcq0 h hcq3 hcq21)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0485 hcq0 h hcq1 hcq3 hcq21 hcq6 hcq7)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0430 h hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0411 hcq0 h hcq1 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0209 h hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0210 hcq0 h hcq1 hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0412 hcq0 h hcq3 hcq21 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0212 h hcq1 hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0213 h hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0214 hcq0 h hcq3 hcq21)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0486 hcq0 h hcq1 hcq3 hcq21 hcq6 hcq7)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0432 h hcq7)
      · exact Or.inr (by exact chamberKills3SpeedTArith0414 hcq0 h hcq1 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0218 h hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0219 hcq0 h hcq1 hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0415 hcq0 h hcq3 hcq21 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0221 h hcq1 hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0222 h hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0223 hcq0 h hcq3 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0416 hcq0 h hcq1 hcq3 hcq21 hcq6)
      · exact Or.inr (by exact chamberKills3SpeedTArith0225 hcq0 h hcq1 hcq21)
      · exact Or.inr (by exact chamberKills3SpeedTArith0226 hcq0 h hcq1 hcq3 hcq21)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0417 hcq0 h hcq1 hcq3 hcq21 hcq6)
  have hrest : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by exact chamberKills3SpeedTArith0228 hcq3 hcq1 hcq21) (by exact chamberKills3SpeedTArith0229 hcq21 hcq3) (by exact chamberKills3SpeedTArith0230 hcq21 hcq3 hcq1) (by exact chamberKills3SpeedTArith0434 hcq3 hcq1 hcq7) (by exact chamberKills3SpeedTArith0418 hcq6) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0231 hApos hcq0 hcq21 hcq3 hcq1)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0232 hcq21 hcq3)) (Or.inr (by exact chamberKills3SpeedTArith0233 hcq0 hcq1 hcq3 hcq21)) (Or.inr (by exact chamberKills3SpeedTArith0234 hApos hcq0 hcq3 hcq1)) (Or.inr (by exact chamberKills3SpeedTArith0235 hcq1 hcq3 hcq21))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  exact Nat.ne_of_gt hdpos hkap

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·DF·DG·FF·FG·GG` dies on the `ν` face `D.natDegree + G.natDegree`, using the kappa-cost band(s). -/
theorem quarticChamberBCDEFG122810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG122810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0487 hApos hcq9 hcq20 hcq1 hAB hcq15 hcq21 hAD hcq5 hcq13 hcq0 hzero)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 4 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 3 * C.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * E.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0258 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0437 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0458 hcq1 h hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0261 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0262 hcq1 hAD h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0438 hcq1 hAD h hcq0 hcq5 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0488 hcq1 hAD h hcq0 hcq8 hcq12 hcq5)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0265 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0440 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0460 hcq1 h hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0268 hcq1 hAD hcq0 h hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0269 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0441 hcq1 h hAD hcq0 hcq5 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0489 hcq1 h hAD hcq0 hcq8 hcq5 hcq12)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * C.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0272 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0443 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0462 hcq1 h hcq12)
      · exact Or.inr (by exact chamberKills3SpeedTArith0275 h hcq1 hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0276 hcq1 h hAD hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0444 hcq1 h hAD hcq0 hcq5 hcq8)
      · exact Or.inr (by exact chamberKills3SpeedTArith0278 hcq1 h hcq0 hcq5)
      · exact Or.inr (by exact chamberKills3SpeedTArith0445 hcq1 h hAD hcq0 hcq5 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0446 hApos hcq1 h hcq0 hcq8 hcq5)
  have hrest : (nuQuarticChamberRest1000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    nuQuarticChamberRest1000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by exact chamberKills3SpeedTArith0281 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0282 hcq1 hAD hcq0 hcq5) (by exact chamberKills3SpeedTArith0447 hcq1 hAD hcq0 hcq5 hcq8) (by exact chamberKills3SpeedTArith0448 hcq1 hAD hcq5 hcq8 hcq0) (by exact chamberKills3SpeedTArith0283 hcq0 hcq5) (by exact chamberKills3SpeedTArith0449 hcq1 hcq0 hcq8) (by exact chamberKills3SpeedTArith0463 hcq1 hcq12) (by exact chamberKills3SpeedTArith0284 hcq1 hAD hcq5 hcq0) (by exact chamberKills3SpeedTArith0490 hcq1 hAD hcq5 hcq8 hcq12 hcq0) (by exact chamberKills3SpeedTArith0285 hcq1 hAD hcq5 hcq0) (by exact chamberKills3SpeedTArith0450 hcq1 hAD hcq8) (by exact chamberKills3SpeedTArith0464 hcq1 hcq12 hcq0) hzl hzbeta (Or.inr (by exact chamberKills3SpeedTArith0491 hApos hcq1 hAD hcq0 hcq5 hcq8 hcq12)) hzdelta (Or.inr (by exact chamberKills3SpeedTArith0452 hApos hcq1 hcq0 hcq5 hcq8)) (Or.inr (by exact chamberKills3SpeedTArith0466 hApos hcq1 hcq0 hcq5 hcq12)) (Or.inr (by exact chamberKills3SpeedTArith0289 hApos hcq1 hcq0 hcq5)) (Or.inr (by exact chamberKills3SpeedTArith0453 hApos hcq1 hcq0 hcq8 hcq5))
  have hlead : (nuQuarticChamberFace1000810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    nuQuarticChamberFace1000810_natDegree A B C D E F G hDne hGne
  rw [degreeZeroNuQuartic810_eq_face1000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hnu
  exact Nat.ne_of_gt hdpos hnu

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`, using the kappa-letter band(s). -/
theorem quarticChamberBCDEFG123810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG123810 A B C D E F G)
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
    exact Nat.ne_of_gt hApos hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by exact chamberKills3SpeedTArith0492 hApos hcq6 hcq7 hcq15 hcq21 hAD hcq13 hcq0 hzero)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact chamberKills3SpeedTArith0044 hAD h hcq0 hcq2)
      · exact Or.inr (by exact chamberKills3SpeedTArith0076 hcq4 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0008 hAD h hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0126 h hcq6 hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0010 h hAD hcq0)
      · exact Or.inr (by exact chamberKills3SpeedTArith0157 h hcq7 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact chamberKills3SpeedTArith0493 hcq4 hcq6 hcq7 h hAD hcq0 hcq2)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by exact chamberKills3SpeedTArith0046 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0047 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0238 hcq4 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0239 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0293 hcq7 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0240 hcq4 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0251 hcq6 hAD hcq0 hcq2) (by exact chamberKills3SpeedTArith0080 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0048 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0421 hcq4 hcq6 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0049 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0241 hcq4 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0081 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0294 hcq7 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0252 hcq6 hAD hcq2 hcq0) (by exact chamberKills3SpeedTArith0351 hcq4 hcq7 hAD hcq0) (by exact chamberKills3SpeedTArith0082 hcq4 hAD hcq0) (by exact chamberKills3SpeedTArith0310 hcq4 hcq6 hAD hcq0) (by exact chamberKills3SpeedTArith0132 hcq6 hAD hcq0) (by exact chamberKills3SpeedTArith0161 hcq7 hcq0) hzl (Or.inr (by exact chamberKills3SpeedTArith0422 hApos hcq4 hcq6 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0423 hApos hcq4 hcq6 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0424 hApos hcq4 hcq6 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0425 hApos hcq4 hcq6 hAD hcq0 hcq2)) (Or.inr (by exact chamberKills3SpeedTArith0426 hApos hcq4 hcq6 hAD hcq0 hcq2)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq7 hApos; omega)) (Or.inr (by exact chamberKills3SpeedTArith0248 hApos hcq4 hcq2 hcq0))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact Nat.ne_of_gt hdpos hpi


end QuarticChamberKills3810

end Max11DegreeRoutes
