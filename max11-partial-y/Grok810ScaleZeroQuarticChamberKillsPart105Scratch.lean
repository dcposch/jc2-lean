import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart01Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart02Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart03Scratch
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
/-- Chamber `BCFG` / `BF·CF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG10810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1216 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq7 hDn hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1217 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq0 hcq7 hEn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1218 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1938 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1939 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1223 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq7 hDn hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1224 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq0 hcq7 hEn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1225 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1940 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1227 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7 hcq3)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1228 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1229 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1230 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq7 hDn hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1231 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq0 hcq7 hEn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1232 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1941 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq7 hcq2 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1234 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7 hcq3)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BF·CF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1235 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1942 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq7 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1943 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq7 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1237 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1944 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq7 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1238 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq0 hcq7)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1474 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1945 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq2 hcq1 h hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq2 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1476 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1240 A.natDegree B.natDegree C.natDegree F.natDegree hApos hcq0 hcq2 h hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq2 hcq6; omega) (by clear * - hcq0 hcq6; omega) (by clear * - hcq2 hcq6; omega) (by clear * - hcq1 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BG·CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq5 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1273 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1274 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1946 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq5 hcq6 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1278 A.natDegree B.natDegree C.natDegree G.natDegree h hcq5 hcq6 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1947 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq5 h hcq6 hcq0 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1280 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1281 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1948 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq5 hcq6 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1285 A.natDegree B.natDegree C.natDegree G.natDegree h hcq5 hcq6 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1949 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq5 h hcq6 hcq0 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1287 A.natDegree B.natDegree C.natDegree G.natDegree hcq6 hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1288 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1950 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq5 h hcq6 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1292 A.natDegree B.natDegree C.natDegree G.natDegree h hcq5 hcq6 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1951 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq5 hcq6 hcq0 hcq2)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq6; omega) (by clear * - hcq0 hcq5 hcq6; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq5 hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq6; omega)) (Or.inr (by clear * - hcq5 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BG·CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG18810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1273 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1274 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1952 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1294 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq6 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1953 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq0 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1280 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1281 A.natDegree B.natDegree C.natDegree G.natDegree h hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1954 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1296 A.natDegree B.natDegree C.natDegree G.natDegree h hcq1 hcq6 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1955 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq6 hcq0 hcq3)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1477 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 h hcq6 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1956 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq3 hcq0 h hcq6 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1478 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1479 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq6 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1957 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hApos hcq3 h hcq0 hcq6)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq3 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq3 hcq5 hcq6; omega) (by clear * - hcq5 hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq3 hcq6; omega) hbl' (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hDn hEn hcq0 hcq4 hcq6 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1241 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq7 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1242 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq7 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1243 A.natDegree B.natDegree C.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1958 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hAC hcq7 hcq2 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1959 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hAC h hcq7 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0229 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0397 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1245 A.natDegree B.natDegree C.natDegree F.natDegree h hAC hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1300 A.natDegree B.natDegree C.natDegree G.natDegree h hAC hcq7 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1246 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq7 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq7)
      · exact absurd h (astra4u_Round4Package_nat_0517 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0403 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1247 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1301 A.natDegree B.natDegree C.natDegree G.natDegree h hAC hcq7 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1248 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq7 hcq0)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq7; omega) (by clear * - hAC hcq7; omega) (by clear * - hcq0; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq3 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCFG22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1249 A.natDegree B.natDegree C.natDegree F.natDegree hcq4 h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1250 A.natDegree B.natDegree C.natDegree F.natDegree hcq4 h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1251 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq9 hDn)
      · exact absurd h (astra4u_Round4Package_nat_1252 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq9 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1253 A.natDegree B.natDegree C.natDegree F.natDegree h hcq4 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1960 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq4 hcq3 hcq0 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1961 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq4 hcq3 h hcq0 hcq9)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1256 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1257 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1258 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq9 hDn)
      · exact absurd h (astra4u_Round4Package_nat_1259 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq9 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1260 A.natDegree B.natDegree C.natDegree F.natDegree h hcq4 hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1962 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq4 hcq3 hcq0 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1262 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq9)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1263 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1264 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq9)
      · exact absurd h (astra4u_Round4Package_nat_1265 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq9 hDn)
      · exact absurd h (astra4u_Round4Package_nat_1266 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 hcq9 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1267 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1963 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq4 hcq3 hcq0 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1269 A.natDegree B.natDegree C.natDegree F.natDegree hApos h hcq0 hcq9)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq4 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq9 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq9 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1964 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq0 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1965 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq0 hcq2 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1966 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq9 hcq0 hcq2 hDn hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1967 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq9 hcq0 hcq2 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1968 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1969 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1970 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1971 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1972 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1973 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq9 hcq0 hcq2 hDn hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1974 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq9 hcq0 hcq2 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1975 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1976 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1977 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1978 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 hcq0 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1979 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1980 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq9 hcq0 hcq2 hDn hcq4)
      · exact absurd h (astra4u_Round4Package_nat_1981 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq9 hcq0 hcq2 hEn hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1982 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq0 hcq2 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1983 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1984 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq0 hcq2 hcq4)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq0 hcq2 hcq4 hcq9; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq9; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·CG·FF·FG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq4 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1985 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq1 hcq9 h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1986 A.natDegree C.natDegree F.natDegree G.natDegree hcq1 hcq9 h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1987 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq1 hcq9 hcq0 hcq5 hDn)
      · exact absurd h (astra4u_Round4Package_nat_1988 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq9 hcq0 hcq5 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1989 A.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1990 A.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1991 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq9 hcq0 hcq5)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq0 hcq5 hcq9; omega) (by clear * - hcq0 hcq1 hcq5 hcq9; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq9; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCFG26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq3 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1270 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1147 A.natDegree C.natDegree F.natDegree hcq9 h)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1148 A.natDegree C.natDegree F.natDegree h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1578 A.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1271 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq9 hcq1 hcq8)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq1 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq8; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `CG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG27810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1992 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq1 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1993 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq1 hcq2 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1304 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq9 hcq1 hDn hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1305 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq9 hcq1 hEn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1994 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1995 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq1 hcq2 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1996 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq1 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ 3 * B.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1309 A.natDegree B.natDegree C.natDegree G.natDegree hcq9 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1310 A.natDegree B.natDegree C.natDegree G.natDegree hcq9 h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1311 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq9 hcq1 hDn hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1312 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq9 hcq1 hEn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1997 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1314 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq1 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1998 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq1 hcq2 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ F.natDegree < C.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < C.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1316 A.natDegree B.natDegree C.natDegree G.natDegree hcq9 hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_1317 A.natDegree B.natDegree C.natDegree G.natDegree hcq9 h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1318 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq9 hcq1 hDn hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1319 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq9 hcq1 hEn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1999 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq9 h hcq2 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1321 A.natDegree B.natDegree C.natDegree G.natDegree h hcq9 hcq1 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2000 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq9 hcq1 hcq0 hcq5)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq1 hcq9; omega) (by clear * - hcq1 hcq5 hcq9; omega) (by clear * - hcq0; omega) (by clear * - hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq9; omega)) (Or.inr (by clear * - hcq1 hcq5 hcq9; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
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
/-- Chamber `BCFG` / `CG·GG` dies on the `μ` face `C.natDegree + G.natDegree`. -/
theorem quarticChamberBCFG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG29810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hEn hcq0 hcq1 hcq2 hcq3 hcq6 hcq7 hcq8 hcq9 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + G.natDegree ∧ B.natDegree + G.natDegree < C.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < C.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2001 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq9 h hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2002 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq9 h hcq2 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1323 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq9 hcq2 hDn)
      · exact absurd h (astra4u_Round4Package_nat_1324 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq0 hcq9 hcq2 hEn)
      · exact Or.inr (astra4u_Round4Package_nat_2003 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq3 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2004 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq9 hcq2 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2005 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq9 h hcq2)
  have hrest : (muQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + G.natDegree :=
    muQuarticChamberRest6810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hcq2 hcq9; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq1; omega) (by clear * - hcq9; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree :=
    muQuarticChamberFace6810_natDegree A B C D E F G hCne hGne
  rw [degreeZeroMuQuartic810_eq_face6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCFG30810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG30810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAC hDn hEn hcq0 hcq4 hcq6 hcq9 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq0 h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1152 A.natDegree C.natDegree F.natDegree hcq2 hAF h)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq4 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1272 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 hcq2 h hAF)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hAF hcq0; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hAF hcq0 hcq4; omega) (by clear * - hAF hcq0 hcq2; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCFG31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAC hDn hEn hcq0 hcq2 hcq6 hcq9 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq2 h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1581 A.natDegree C.natDegree F.natDegree G.natDegree hAF h hcq0 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2006 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq2 h hAF hcq0 hcq5)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hAF hcq2; omega) (by clear * - hAF hcq0 hcq2 hcq5; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hAF hcq0 hcq2 hcq5; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCFG32810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG32810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAC hAF hDn hEn hcq1 hcq4 hcq6 hcq9 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1483 A.natDegree B.natDegree F.natDegree G.natDegree hcq0 hAG hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_1586 A.natDegree C.natDegree F.natDegree G.natDegree hcq3 hAG h hcq4)
      · exact absurd h (astra4u_Round4Package_nat_0222 A.natDegree D.natDegree hApos hDn)
      · exact absurd h (astra4u_Round4Package_nat_0391 A.natDegree E.natDegree hApos hEn)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2007 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hApos hcq3 h hAG hcq1)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BCFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz hEz (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq3; omega) (by clear * - hAG hcq1 hcq3; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq0 hcq3; omega) (by clear * - hAG hcq0 hcq1; omega) (by clear * - hAG hcq3; omega) (by clear * - hcq4; omega) (by clear * - hAG hcq3; omega) hbl' (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hAG hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBDEF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1099 A.natDegree B.natDegree C.natDegree F.natDegree hcq6 hCn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1399 A.natDegree B.natDegree E.natDegree F.natDegree h hcq3 hcq6 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq6 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1103 A.natDegree B.natDegree F.natDegree G.natDegree hcq6 hcq5 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2008 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq6 hcq2 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1106 A.natDegree B.natDegree C.natDegree F.natDegree hcq6 hCn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1401 A.natDegree B.natDegree E.natDegree F.natDegree hcq3 h hcq6 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq6 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1110 A.natDegree B.natDegree F.natDegree G.natDegree hcq6 hcq5 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2009 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq6 hcq2 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_1113 A.natDegree B.natDegree C.natDegree F.natDegree hcq6 hCn hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1403 A.natDegree B.natDegree E.natDegree F.natDegree hcq3 h hcq6 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq6 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1117 A.natDegree B.natDegree F.natDegree G.natDegree hcq6 hcq5 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1346 A.natDegree B.natDegree D.natDegree F.natDegree h hcq2 hcq5)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq5 hcq6; omega) (by clear * - hcq0; omega) (by clear * - hcq3 hcq5 hcq6; omega) (by clear * - hcq2; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq2 hcq5 hcq6; omega)) (Or.inr (by clear * - hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBDEF3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1692 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_2010 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq6 hcq0 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1694 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2011 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq6 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1696 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1697 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 hcq0 hcq2 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2012 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hcq0 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1699 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_2013 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq6 hcq0 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1701 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2014 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1703 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1704 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 hcq0 hcq2 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2015 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hcq0 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1706 A.natDegree B.natDegree D.natDegree F.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_2016 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq6 hcq0 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1708 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2017 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq6 hcq0 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1710 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1711 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq6 hcq0 hcq2 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2018 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq6 hcq0 hcq2)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq1 hcq2 hcq6; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBDEF5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF5810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2019 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2020 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2021 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2022 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2023 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2024 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2025 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2026 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2027 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2028 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq8 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBDEF8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF8810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1348 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2029 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq3 hcq6 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2030 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq6 hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1351 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1352 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2031 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq3 h hcq6 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2032 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos hcq3 h hcq6 hcq1 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq6; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq3 hcq6; omega) (by clear * - hcq1 hcq3 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBDEF9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF9810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_2033 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hcq6 hcq0 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2034 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1818 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1819 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2035 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq6 hcq0 hcq3 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2036 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq6 hcq0 hcq3)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1822 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_2037 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hcq6 hcq0 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2038 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1824 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1825 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2039 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq6 hcq0 hcq3 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2040 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq6 hcq0 hcq3)
  have hbdelta' : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1828 A.natDegree B.natDegree F.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_2041 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hcq6 hcq0 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2042 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1831 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1832 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq6 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2043 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq6 hcq0 hcq3 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2044 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq6 hcq0 hcq3)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq4 hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq4 hcq6; omega) (by clear * - hcq0 hcq1 hcq3 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq6 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBDEF11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hCn hGn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1404 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2045 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq8 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1405 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1406 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2046 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq0 hcq8 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1408 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq8)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2047 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq8 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1409 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1410 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2048 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq8 hcq5)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq1 hcq5 hcq8; omega) (by clear * - hcq0 hcq1 hcq5; omega) (by clear * - hcq0 hcq1 hcq5 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBDEF12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1412 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq4 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2049 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq4 h hcq6 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq6 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1414 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 hcq4 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2050 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos hcq0 hcq4 h hcq6 hcq3)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq4 hcq6; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEF13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1357 A.natDegree B.natDegree D.natDegree hcq7 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1358 A.natDegree B.natDegree D.natDegree hAB hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_2051 A.natDegree B.natDegree D.natDegree E.natDegree h hcq1 hAB hAD)
      · exact Or.inr (astra4u_Round4Package_nat_1359 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hAD hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2052 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hAB hcq7 hAD hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1084 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1085 A.natDegree B.natDegree D.natDegree hApos h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1330 A.natDegree B.natDegree D.natDegree E.natDegree hcq1 hAB h)
      · exact Or.inr (astra4u_Round4Package_nat_1361 A.natDegree B.natDegree D.natDegree F.natDegree h hAB hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2053 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos hcq1 h hcq6 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1087 A.natDegree B.natDegree D.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1088 A.natDegree B.natDegree D.natDegree hApos h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1332 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq1 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1363 A.natDegree B.natDegree D.natDegree F.natDegree hAB h hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1070 A.natDegree G.natDegree hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1364 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq0)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq7; omega) (by clear * - hcq0; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq2; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq6 hApos; omega))
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
/-- Chamber `BDEF` / `DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBDEF15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF15810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2054 A.natDegree B.natDegree D.natDegree F.natDegree hAD h hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1591 A.natDegree D.natDegree F.natDegree hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1592 A.natDegree D.natDegree E.natDegree F.natDegree h hAD hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1593 A.natDegree D.natDegree F.natDegree h hAD hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2055 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hAD hcq0 hcq1 hcq5)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1; omega) hbl' (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEF19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hGn hcq0 hcq1 hcq4 hcq8 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2056 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hcq6 hAE h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2057 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hAE h hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2058 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hcq4 hAE hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2059 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hAE hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2060 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq8 hAE h hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1093 A.natDegree B.natDegree E.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1337 A.natDegree B.natDegree D.natDegree E.natDegree hcq8 hAE h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1094 A.natDegree B.natDegree E.natDegree hApos hcq8 h)
      · exact Or.inr (astra4u_Round4Package_nat_1420 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hAE hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2061 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos hcq8 h hcq1 hcq0)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1096 A.natDegree B.natDegree E.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1339 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq8 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1097 A.natDegree B.natDegree E.natDegree hApos hcq8 h)
      · exact Or.inr (astra4u_Round4Package_nat_1422 A.natDegree B.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1070 A.natDegree G.natDegree hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2062 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq1 hcq0)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hcq8; omega) (by clear * - hcq0; omega) (by clear * - hcq1; omega) (by clear * - hcq8; omega) (by clear * - hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEF21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hCn hGn hcq0 hcq2 hcq3 hcq8 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1424 A.natDegree B.natDegree E.natDegree F.natDegree hAE h hcq0 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1608 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2063 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hAE hcq0 hcq2 hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq5; omega) hbl' (Or.inr (by clear * - hAE hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBDEF22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF22810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hAD hAE hCn hGn hcq0 hcq1 hcq4 hcq6 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1124 A.natDegree B.natDegree F.natDegree hcq0 h hAF)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1175 A.natDegree E.natDegree F.natDegree h hAF hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2064 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hAF hcq4 hcq1)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hGz (by clear * - hAF hcq0; omega) (by clear * - hAF hcq0 hcq4; omega) (by clear * - hAF hcq0 hcq1; omega) (by clear * - hcq1; omega) (by clear * - hAF hcq0 hcq1 hcq4; omega) hbl' (Or.inr (by clear * - hAF hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hAF hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG3810 A B C D E F G)
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
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1367 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq6 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1368 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2065 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1370 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq2 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1371 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq6 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2066 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1374 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq6 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1375 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2067 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1377 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq2 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1378 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq6 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2068 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1380 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_1381 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq6 hCn hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1382 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2069 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq2)
      · exact absurd h (astra4u_Round4Package_nat_1384 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq2 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1385 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq6 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1386 A.natDegree B.natDegree D.natDegree h hcq2)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq1 hcq2 hcq6; omega) (by clear * - hcq0 hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBDEG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG5810 A B C D E F G)
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
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq2 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2071 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2072 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq2 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2073 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq2 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2074 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq2 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2076 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2077 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq2 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2078 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq2 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2079 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq2 hcq1)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq1 hcq2 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq1 hcq2 hcq6; omega) (by clear * - hcq1 hcq2 hcq6; omega) (by clear * - hcq2 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·DD·DE·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBDEG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG6810 A B C D E F G)
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
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2070 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1367 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq6 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2080 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2081 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1370 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq3 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2082 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2083 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2075 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1374 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq6 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2084 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2085 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1377 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq3 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2086 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2087 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2088 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 hcq6 h hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1381 A.natDegree B.natDegree C.natDegree D.natDegree G.natDegree hcq0 hcq6 hCn hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2089 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2090 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1384 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq3 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_2091 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2092 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1 hcq3)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq1 hcq3 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq1 hcq3 hcq6; omega) (by clear * - hcq1 hcq3 hcq6; omega) (by clear * - hcq3 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq6; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG8810 A B C D E F G)
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
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1366 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1387 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2093 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hcq6 hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1388 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq6 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2094 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1373 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1390 A.natDegree B.natDegree D.natDegree G.natDegree hcq0 h hcq6 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2095 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1391 A.natDegree B.natDegree D.natDegree G.natDegree h hcq0 hcq6 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2096 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq0 h hcq6 hcq1 hcq3)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq3 hcq6; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG9810 A B C D E F G)
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
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq3 hcq4 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1430 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq4 hcq0 hcq6 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2097 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq4 h hcq0 hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1432 A.natDegree B.natDegree E.natDegree G.natDegree h hcq4 hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1433 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 hcq6 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1434 A.natDegree B.natDegree E.natDegree G.natDegree h hcq4 hcq0 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2098 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq4 h hcq0 hcq6 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1437 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq4 hcq0 hcq6 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2099 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq4 h hcq0 hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1439 A.natDegree B.natDegree E.natDegree G.natDegree hcq4 h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1440 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 hcq6 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1441 A.natDegree B.natDegree E.natDegree G.natDegree h hcq4 hcq0 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2100 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq4 h hcq0 hcq6 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1443 A.natDegree B.natDegree E.natDegree G.natDegree hcq0 hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_1444 A.natDegree B.natDegree C.natDegree E.natDegree G.natDegree hcq4 hcq0 hcq6 hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2101 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq4 h hcq0 hcq6 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1446 A.natDegree B.natDegree E.natDegree G.natDegree hcq4 h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1447 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 hcq6 hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1448 A.natDegree B.natDegree E.natDegree G.natDegree h hcq4 hcq0 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2102 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree h hcq4 hcq0 hcq2)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq4 hcq6; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq4 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq6; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBDEG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG11810 A B C D E F G)
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
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq3 hcq6 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + G.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1429 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2103 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1449 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1450 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2104 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1436 A.natDegree B.natDegree E.natDegree G.natDegree h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_2105 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1452 A.natDegree B.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1453 A.natDegree B.natDegree E.natDegree G.natDegree h hcq1 hcq0 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2106 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 h hcq0 hcq6 hcq4)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `BG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBDEG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG12810 A B C D E F G)
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
    exact hnc (by clear * - hCn hFn hcq0 hcq1 hcq4 hcq6 hzero; omega)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq3 hcq5 hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq3 hcq5 hcq6; omega) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBDEG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG13810 A B C D E F G)
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
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1081 A.natDegree B.natDegree D.natDegree hcq7 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1082 A.natDegree B.natDegree D.natDegree hAB hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1328 A.natDegree B.natDegree D.natDegree E.natDegree h hcq1 hAB hAD)
      · exact absurd h (astra4u_Round4Package_nat_0224 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1393 A.natDegree B.natDegree D.natDegree G.natDegree h hcq2 hAB hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2107 A.natDegree B.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq2 hAB h hAD)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1084 A.natDegree B.natDegree D.natDegree h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1085 A.natDegree B.natDegree D.natDegree hApos h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1330 A.natDegree B.natDegree D.natDegree E.natDegree hcq1 hAB h)
      · exact absurd h (astra4u_Round4Package_nat_0231 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1395 A.natDegree B.natDegree D.natDegree G.natDegree h hcq2 hAB)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1331 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq1 h hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1087 A.natDegree B.natDegree D.natDegree hcq6 h)
      · exact absurd h (astra4u_Round4Package_nat_0730 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1088 A.natDegree B.natDegree D.natDegree hApos h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1332 A.natDegree B.natDegree D.natDegree E.natDegree hApos hcq1 h hcq6)
      · exact absurd h (astra4u_Round4Package_nat_0404 A.natDegree F.natDegree hApos hFn)
      · exact Or.inr (astra4u_Round4Package_nat_1396 A.natDegree B.natDegree D.natDegree G.natDegree hApos h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1089 A.natDegree B.natDegree D.natDegree hApos h)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hFz (by clear * - hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq1; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq6 hApos; omega)) (Or.inr (by clear * - hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

end QuarticChamberKills810

end Max11DegreeRoutes
