import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart06Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart07Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart08Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart09Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart10Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart101Scratch

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
/-- Chamber `BDEG` / `DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBDEG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hCn hFn hcq0 hcq1 hcq5 hcq6 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2108 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq1 hAD h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1614 A.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1615 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1616 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2109 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq5 hcq1 h hAD hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG18810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1397 A.natDegree B.natDegree D.natDegree G.natDegree hcq2 hcq0 hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1054 A.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hAD hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2110 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq2 hcq0 h hAD hcq5)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hAD hcq0 hcq2; omega) (by clear * - hAD hcq0 hcq2 hcq5; omega) (by clear * - hcq0 hcq5; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG19810 A B C D E F G)
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
    exact hnc (by clear * - hAD hCn hFn hcq0 hcq1 hcq4 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1333 A.natDegree B.natDegree D.natDegree E.natDegree hcq8 hcq6 h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1334 A.natDegree B.natDegree D.natDegree E.natDegree hcq8 hAE h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1335 A.natDegree B.natDegree D.natDegree E.natDegree h hcq8 hAE hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2111 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq8 hAE hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2112 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq8 hAE h hcq1 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1093 A.natDegree B.natDegree E.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1337 A.natDegree B.natDegree D.natDegree E.natDegree hcq8 hAE h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1094 A.natDegree B.natDegree E.natDegree hApos hcq8 h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1457 A.natDegree B.natDegree E.natDegree G.natDegree h hcq8 hAE hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1338 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq8 h hcq1)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1096 A.natDegree B.natDegree E.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1339 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq8 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1097 A.natDegree B.natDegree E.natDegree hApos hcq8 h)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1458 A.natDegree B.natDegree E.natDegree G.natDegree h hcq8 hAE hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1340 A.natDegree B.natDegree D.natDegree E.natDegree hApos h hcq1)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG21810 A B C D E F G)
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
    exact hnc (by clear * - hAD hCn hFn hcq0 hcq2 hcq3 hcq8 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2113 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2114 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq2 hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2115 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq2 hcq3 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2116 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hAE hcq2 hcq3 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2117 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hAE h hcq2 hcq3 hcq0)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq3; omega) (by clear * - hAE hcq0 hcq2; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBDEG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hAE hCn hFn hcq0 hcq1 hcq4 hcq6 hApos hzero; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hAG hcq0; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq0; omega) (by clear * - hAG hcq0 hcq1 hcq4; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq1 hcq4; omega) (Or.inr (by clear * - hAG hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBDFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG1810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1099 A.natDegree B.natDegree C.natDegree F.natDegree hcq7 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1101 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1463 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2118 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq2 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1106 A.natDegree B.natDegree C.natDegree F.natDegree hcq7 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1108 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1465 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1344 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_1113 A.natDegree B.natDegree C.natDegree F.natDegree hcq7 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1115 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1466 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1346 A.natDegree B.natDegree D.natDegree F.natDegree h hcq2 hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq4 hcq7; omega) (by clear * - hcq1; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq2 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·BG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBDFG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG3810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1099 A.natDegree B.natDegree C.natDegree F.natDegree hcq7 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1101 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1467 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2119 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1106 A.natDegree B.natDegree C.natDegree F.natDegree hcq7 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1108 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1469 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1344 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_1113 A.natDegree B.natDegree C.natDegree F.natDegree hcq7 hCn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1115 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1470 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1346 A.natDegree B.natDegree D.natDegree F.natDegree h hcq2 hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq4 hcq7; omega) (by clear * - hcq1; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq2 hcq4 hcq7; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·BG·FF·FG·GG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBDFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG8810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq1 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1471 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2120 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq1 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1473 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1356 A.natDegree B.natDegree D.natDegree F.natDegree hApos hcq1 h hcq7 hcq5)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq1 hcq7; omega) (by clear * - hcq1 hcq5; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBDFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1692 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_2010 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq0 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1694 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1695 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq0 hcq2 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1696 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2121 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq7 hcq0 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2122 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq1 h hcq7 hcq0 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1699 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_2013 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq0 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1701 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1702 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq0 hcq2 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1703 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2123 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq7 hcq0 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2124 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1706 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_2016 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 hcq0 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1708 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1709 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq7 hcq0 hcq2 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1710 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2125 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq7 hcq0 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2126 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq2)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq1 hcq2 hcq7; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBDFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG11810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1348 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2127 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hcq7 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2128 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq3 h hcq7 hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1351 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1352 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_2129 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq3 hcq7 hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1354 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq7 hcq1 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBDFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG12810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1474 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2130 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq1 h hcq7 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1476 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1356 A.natDegree B.natDegree D.natDegree F.natDegree hApos hcq0 h hcq7 hcq3)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BG·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDFG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG15810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1367 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq7 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1368 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1369 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq7 hcq3 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2131 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1371 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2132 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1374 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq7 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1375 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1376 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq7 hcq3 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2133 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1378 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2134 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq3)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1380 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_1381 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq7 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1382 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1383 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq7 hcq3 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2135 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1385 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2136 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq3)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

end QuarticChamberKills810

end Max11DegreeRoutes
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
/-- Chamber `BDFG` / `BG·DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG17810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1387 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2137 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1388 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2138 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1390 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq7 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2139 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1391 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq7 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2140 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq1 hcq6)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBDFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG18810 A B C D E F G)
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
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hEn hcq0 hcq1 hcq2 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1477 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2141 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq4 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1478 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1479 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2142 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq0 hcq7 hcq4)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq6 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq4 hcq7; omega) hbl' (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG19810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1357 A.natDegree B.natDegree D.natDegree hcq8 h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1358 A.natDegree B.natDegree D.natDegree hAB hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1359 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hAD hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2143 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hAB hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2144 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq3 h hAB hcq8 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1084 A.natDegree B.natDegree D.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1085 A.natDegree B.natDegree D.natDegree hApos h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1361 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1395 A.natDegree B.natDegree D.natDegree G.natDegree h hcq3 hAB)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1362 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq7 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1087 A.natDegree B.natDegree D.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1088 A.natDegree B.natDegree D.natDegree hApos h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1363 A.natDegree B.natDegree D.natDegree F.natDegree hAB h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1396 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1364 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq0)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq8; omega) (by clear * - hcq0; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG23810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1397 A.natDegree B.natDegree D.natDegree G.natDegree hcq3 hcq0 hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2145 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq0 h hAD hcq4)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hAD hcq0 hcq3; omega) (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq4; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBDFG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hCn hEn hcq0 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq0 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq5 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2146 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq5 h hAF hcq2)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hAF hcq0; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hcq2; omega) (by clear * - hAF hcq0 hcq5; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBDFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hCn hEn hcq0 hcq2 hcq4 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq2 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2147 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq2 h hAF hcq0 hcq4)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hAF hcq2; omega) (by clear * - hAF hcq2 hcq4; omega) (by clear * - hcq4; omega) (by clear * - hAF hcq0 hcq2; omega) hbl' (Or.inr (by clear * - hAF hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hAF hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBDFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG26810 A B C D E F G)
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
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hAF hCn hEn hcq1 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1483 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 hAG hcq1 h)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1627 A.natDegree D.natDegree F.natDegree G.natDegree hcq3 hcq2 hAG h)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2148 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hApos hcq2 h hAG hcq1)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq2; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq1 hcq2; omega) (by clear * - hcq5; omega) (by clear * - hAG hcq1 hcq2; omega) hbl' (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hAG hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG1810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1399 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1463 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2149 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq0 h hcq7 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1401 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1465 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1402 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq7 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1403 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1466 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1118 A.natDegree B.natDegree F.natDegree h hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq4 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq4 hcq7; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·BG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBEFG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG3810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2150 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1467 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2151 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq3 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2152 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1469 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2153 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq3 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2154 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1470 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1118 A.natDegree B.natDegree F.natDegree h hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq4 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq4 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq4 hcq7; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·BG·FF·FG·GG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBEFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG8810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2150 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq1 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1471 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2155 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq1 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2152 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1473 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2156 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq0 hcq7 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq6 hcq7; omega) (by clear * - hcq0 hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBEFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1818 A.natDegree B.natDegree E.natDegree F.natDegree h hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1819 A.natDegree B.natDegree E.natDegree F.natDegree h hcq2 hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2157 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq7 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2158 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq1 h hcq7 hcq0)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1822 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1824 A.natDegree B.natDegree E.natDegree F.natDegree hcq2 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1825 A.natDegree B.natDegree E.natDegree F.natDegree h hcq2 hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2159 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq7 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2160 A.natDegree B.natDegree E.natDegree F.natDegree hcq2 h hcq7 hcq0)
  have hbdelta' : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1828 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1831 A.natDegree B.natDegree E.natDegree F.natDegree hcq2 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1832 A.natDegree B.natDegree E.natDegree F.natDegree hcq2 h hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2161 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq1 hcq7 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2162 A.natDegree B.natDegree E.natDegree F.natDegree h hcq2 hcq7 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq2 hcq7; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBEFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq3 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1404 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1405 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1406 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2163 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1407 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq8)
  have hbbeta' : beta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1408 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1409 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1410 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2164 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq8 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1411 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq8)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq1 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi

end QuarticChamberKills810

end Max11DegreeRoutes
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
/-- Chamber `BEFG` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBEFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG12810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1412 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq2 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1474 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2165 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq2 hcq1 h hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1414 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 hcq2 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1476 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1415 A.natDegree B.natDegree E.natDegree F.natDegree hApos hcq0 hcq2 h hcq7)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BG·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBEFG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG15810 A B C D E F G)
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
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq3 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1430 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 hcq0 hcq7 hCn)
      · exact absurd h (astra4u_Round4Package_nat_1431 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq0 hcq7 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1432 A.natDegree B.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2166 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq0 hcq7 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1434 A.natDegree B.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2167 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq0 hcq7 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1437 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 hcq0 hcq7 hCn)
      · exact absurd h (astra4u_Round4Package_nat_1438 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq0 hcq7 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1439 A.natDegree B.natDegree E.natDegree G.natDegree hcq3 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2168 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq0 hcq7 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1441 A.natDegree B.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2169 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq0 hcq7 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1443 A.natDegree B.natDegree E.natDegree G.natDegree hcq0 hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_1444 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq3 hcq0 hcq7 hCn)
      · exact absurd h (astra4u_Round4Package_nat_1445 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq3 hcq0 hcq7 hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1446 A.natDegree B.natDegree E.natDegree G.natDegree hcq3 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2170 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq0 hcq7 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1448 A.natDegree B.natDegree E.natDegree G.natDegree h hcq3 hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2171 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq3 hcq0 hcq2)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BG·EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBEFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG17810 A B C D E F G)
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
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq3 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1449 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2172 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1450 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2173 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1452 A.natDegree B.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2174 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1453 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2175 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq4)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBEFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq2 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1477 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 h hcq7 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2176 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq0 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1478 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1479 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2177 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos hcq4 h hcq0 hcq7)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq6 hcq7; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq4 hcq6 hcq7; omega) hbl' (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBEFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG19810 A B C D E F G)
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
    exact hnc (by clear * - hCn hDn hcq0 hcq2 hcq3 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1416 A.natDegree B.natDegree E.natDegree F.natDegree hcq8 hcq7 hAE h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1417 A.natDegree B.natDegree E.natDegree F.natDegree h hcq8 hcq2 hAE)
      · exact Or.inr (astra4u_Round4Package_nat_1418 A.natDegree B.natDegree E.natDegree F.natDegree h hcq2 hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2178 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hcq2 hAE hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2179 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq8 hAE h hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1093 A.natDegree B.natDegree E.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1094 A.natDegree B.natDegree E.natDegree hApos hcq8 h)
      · exact Or.inr (astra4u_Round4Package_nat_1420 A.natDegree B.natDegree E.natDegree F.natDegree h hcq2 hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1457 A.natDegree B.natDegree E.natDegree G.natDegree h hcq8 hAE hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1421 A.natDegree B.natDegree E.natDegree F.natDegree hApos hcq8 h hcq0)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1096 A.natDegree B.natDegree E.natDegree hcq7 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1097 A.natDegree B.natDegree E.natDegree hApos hcq8 h)
      · exact Or.inr (astra4u_Round4Package_nat_1422 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1458 A.natDegree B.natDegree E.natDegree G.natDegree h hcq8 hAE hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1423 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq0)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq8; omega) (by clear * - hcq0; omega) (by clear * - hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq3 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq7 hcq8 hApos; omega)) (Or.inr (by clear * - hcq7 hcq8; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `EE·EF·EG·FF·FG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBEFG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG21810 A B C D E F G)
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
    exact hnc (by clear * - hCn hDn hcq0 hcq1 hcq5 hcq8 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1424 A.natDegree B.natDegree E.natDegree F.natDegree hAE h hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2180 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2181 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq5 hcq1)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hAE hcq0 hcq5; omega) (by clear * - hcq5; omega) (by clear * - hAE hcq0 hcq5; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBEFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG22810 A B C D E F G)
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
    exact hnc (by clear * - hCn hDn hcq0 hcq2 hcq3 hcq4 hcq8 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1424 A.natDegree B.natDegree E.natDegree F.natDegree hAE h hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2182 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2183 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq2 hcq4)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq2; omega) (by clear * - hAE hcq0 hcq2; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBEFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG23810 A B C D E F G)
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
    exact hnc (by clear * - hCn hDn hcq0 hcq2 hcq3 hcq4 hcq8 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2184 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq3 hcq2 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_2185 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hAE hcq3 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1418 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hAE hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2186 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hAE hcq3 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2187 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq3 hcq0)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hAE hcq0 hcq3; omega) (by clear * - hcq2; omega) (by clear * - hAE hcq0 hcq3; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBEFG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAE hCn hDn hcq0 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq0 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1175 A.natDegree E.natDegree F.natDegree h hAF hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq5 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1428 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 h hAF hcq2)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hAF hcq0; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hAF hcq0 hcq5; omega) (by clear * - hcq4; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBEFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAE hCn hDn hcq0 hcq2 hcq4 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq2 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1631 A.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2188 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hAF hcq0 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hAF hcq2; omega) (by clear * - hAF hcq0 hcq2 hcq6; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hcq6; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BEFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBEFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAE hAF hCn hDn hcq1 hcq2 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1483 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 hAG hcq1 h)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact Or.inr (astra4u_Round4Package_nat_1636 A.natDegree E.natDegree F.natDegree G.natDegree h hAG hcq5 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2189 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hApos h hAG hcq1 hcq2)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hcq5; omega) (by clear * - hAG hcq0 hcq2; omega) hbl' (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAG hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEF` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberCDEF0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq6 hcq7 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1493 A.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1494 A.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2190 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAC hcq1 hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1495 A.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2191 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hAC h hcq8)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1129 A.natDegree C.natDegree D.natDegree hApos h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1130 A.natDegree C.natDegree D.natDegree hAC h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1487 A.natDegree C.natDegree D.natDegree E.natDegree hAC h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1497 A.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1498 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq1; omega) (by clear * - hAC hcq0 hcq1; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

end QuarticChamberKills810

end Max11DegreeRoutes
