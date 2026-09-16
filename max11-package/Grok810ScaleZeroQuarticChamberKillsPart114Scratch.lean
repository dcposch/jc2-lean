import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart101Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart102Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart103Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart104Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart105Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch

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
/-- Chamber `DEFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberDEFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG12810 A B C D E F G)
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
    exact hnc (by clear * - hAD hAE hBn hCn hcq0 hcq4 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1175 A.natDegree E.natDegree F.natDegree h hAF hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq7 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2823 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hAF hcq4 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1173 A.natDegree D.natDegree F.natDegree hAF h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1177 A.natDegree E.natDegree F.natDegree hAF h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1580 A.natDegree F.natDegree G.natDegree h hcq7 hAF)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1613 A.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq4 hcq0)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hcq0; omega) (by clear * - hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0; omega)) (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberDEFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG13810 A B C D E F G)
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
    exact hnc (by clear * - hAD hAE hBn hCn hcq0 hcq2 hcq6 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1631 A.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2824 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq2 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1173 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1633 A.natDegree E.natDegree F.natDegree G.natDegree hAF h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1584 A.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2825 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq0 hcq2 hcq8)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hcq2; omega) (by clear * - hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `DEFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberDEFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG14810 A B C D E F G)
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
    exact hnc (by clear * - hAD hAE hAF hBn hCn hcq0 hcq4 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0221 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1627 A.natDegree D.natDegree F.natDegree G.natDegree hcq2 hcq0 hAG h)
      · exact Or.inr (astra4u_Round4Package_nat_1636 A.natDegree E.natDegree F.natDegree G.natDegree h hAG hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2826 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq0 h hAG hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact absurd h (astra4u_Round4Package_nat_0228 A.natDegree C.natDegree hApos hCn)
      · exact Or.inr (astra4u_Round4Package_nat_1629 A.natDegree D.natDegree F.natDegree G.natDegree hcq2 hcq0 hAG h)
      · exact Or.inr (astra4u_Round4Package_nat_1638 A.natDegree E.natDegree F.natDegree G.natDegree hAG h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1182 A.natDegree F.natDegree G.natDegree h hAG hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1183 A.natDegree F.natDegree G.natDegree hApos h hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2827 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq0 h hcq7 hcq4)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hcq7; omega) (by clear * - hAG hcq0 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega)) (Or.inr (by clear * - hcq0 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1399 A.natDegree B.natDegree E.natDegree F.natDegree h hcq4 hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq7 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1103 A.natDegree B.natDegree F.natDegree G.natDegree hcq7 hcq6 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2828 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq4 h hcq7 hcq3 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1401 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq7 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1110 A.natDegree B.natDegree F.natDegree G.natDegree hcq7 hcq6 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2820 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq4 h hcq7 hcq3 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1212 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1403 A.natDegree B.natDegree E.natDegree F.natDegree hcq4 h hcq7 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq7 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1117 A.natDegree B.natDegree F.natDegree G.natDegree hcq7 hcq6 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1673 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq7 hcq3 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq7; omega) (by clear * - hcq6 hcq7; omega) (by clear * - hcq1; omega) (by clear * - hcq4 hcq6 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq4 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·CF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1674 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1798 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq4 hcq0 hcq8 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1218 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1219 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq8 hcq6 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2829 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq0 hcq8 hcq3 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1676 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1800 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 h hcq0 hcq8 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1225 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1226 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq8 hcq6 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2830 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq0 hcq8 hcq3 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1228 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1229 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1678 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1802 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq4 h hcq0 hcq8 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1232 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8 hcq6)
      · exact absurd h (astra4u_Round4Package_nat_1233 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq0 hcq8 hcq6 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1679 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq8 hcq3 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq8; omega) (by clear * - hcq0 hcq6 hcq8; omega) (by clear * - hcq1; omega) (by clear * - hcq0 hcq4 hcq6 hcq8; omega) (by clear * - hcq3 hcq8; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq3; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq8; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq4 hcq6 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq6 hcq8; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·CF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF8810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1680 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1681 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1682 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2831 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq3 hcq8 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1683 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq8 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2832 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq3 hcq8 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1685 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1686 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1687 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2833 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq3 hcq8 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1688 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq8 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2834 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq3 hcq8 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq3 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq3 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq3 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8; omega) (by clear * - hcq0 hcq3 hcq8; omega) (by clear * - hcq3 hcq8; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8; omega) (by clear * - hcq3 hcq8; omega) (by clear * - hcq1 hcq2 hcq8; omega) (by clear * - hcq0 hcq2 hcq3 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·CF·DD·DE·EE` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2467 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2468 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2469 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2835 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq8 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2471 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_2836 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq8 hcq1 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2837 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq8 hcq1 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2474 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2475 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2476 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2838 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq8 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2478 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_2839 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq8 hcq1 hcq4 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2840 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq8 hcq1 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2481 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2482 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2483 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2841 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq8 hcq1 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2485 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq1 hcq4)
      · exact absurd h (astra4u_Round4Package_nat_2842 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq8 hcq1 hcq4 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2843 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq8 hcq1 hcq4)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq4 hcq8; omega) (by clear * - hcq1 hcq4 hcq8; omega) (by clear * - hcq1 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq4 hcq8; omega) (by clear * - hcq1 hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq8; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·CF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF11810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1680 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1681 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1682 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2844 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq0 hcq2 hcq8 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1683 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq8 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2845 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq0 hcq2 hcq8 hcq1)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1685 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1686 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1687 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2846 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq0 hcq2 hcq8 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1688 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq8 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2847 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq0 hcq2 hcq8 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq4 hcq8; omega) (by clear * - hcq1 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq2 hcq8; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8; omega) (by clear * - hcq2 hcq8; omega) (by clear * - hcq1 hcq4 hcq8; omega) (by clear * - hcq0 hcq2 hcq4 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·CF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEF14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq2 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1803 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1804 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2488 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1805 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1806 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2848 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 h hcq0 hcq1 hcq8 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1808 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1809 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2490 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1810 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq2 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1811 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2849 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq8 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq1 hcq2 hcq6 hcq8; omega) (by clear * - hcq0 hcq6 hcq8; omega) (by clear * - hcq8; omega) (by clear * - hcq1 hcq2 hcq6; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq8; omega) (by clear * - hcq0 hcq1 hcq2 hcq8; omega) (by clear * - hcq1 hcq2 hcq6 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·CF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1674 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1813 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq1 hcq5 hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1235 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2850 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq5 h hcq0 hcq8 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1676 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq8 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1815 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 hcq5 h hcq0 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1237 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq8)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2851 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq5 h hcq0 hcq8 hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq8; omega) (by clear * - hcq1 hcq4; omega) (by clear * - hcq0 hcq1 hcq5 hcq8; omega) (by clear * - hcq4 hcq8; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq4; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hcq4 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1692 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1693 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1694 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2011 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq7 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1696 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1697 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq0 hcq3 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2852 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq2 h hcq7 hcq0 hcq3)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1699 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1700 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1701 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2014 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq2 h hcq7 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1703 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1704 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq0 hcq3 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2853 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq2 h hcq7 hcq0 hcq3)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1706 A.natDegree B.natDegree D.natDegree F.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1707 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1708 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2017 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq2 h hcq7 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1710 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq3)
      · exact absurd h (astra4u_Round4Package_nat_1711 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree hcq7 hcq0 hcq3 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2854 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq7 hcq0 hcq3)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq2 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq2 hcq7; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq7; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq7; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF18810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2019 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2855 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2020 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2021 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2022 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2856 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq1 hcq2 hcq10 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2024 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2857 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2025 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2026 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2027 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq10 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2858 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq1 hcq2 hcq10 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq0 hcq2 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq10; omega) (by clear * - hcq0 hcq1 hcq6 hcq10; omega) (by clear * - hcq1 hcq2 hcq6 hcq10; omega) (by clear * - hcq0 hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi

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
/-- Chamber `BCDEF` / `BF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF21810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1713 A.natDegree B.natDegree C.natDegree F.natDegree hcq3 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1348 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2029 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq7 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1349 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2859 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq4 h hcq7 hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1351 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1715 A.natDegree B.natDegree C.natDegree F.natDegree hcq3 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1352 A.natDegree B.natDegree D.natDegree F.natDegree hApos h hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2031 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq7 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2860 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq3 hcq4 h hcq7 hcq1 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq3 hcq7; omega) (by clear * - hcq0 hcq3 hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·EE` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF22810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF22810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1347 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1713 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2034 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1818 A.natDegree B.natDegree E.natDegree F.natDegree h hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1819 A.natDegree B.natDegree E.natDegree F.natDegree h hcq5 hcq7 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2035 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq7 hcq0 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2861 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq5 h hcq7 hcq0 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1822 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1715 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2038 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1824 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1825 A.natDegree B.natDegree E.natDegree F.natDegree h hcq5 hcq7 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2039 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq7 hcq0 hcq4 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2862 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq5 h hcq7 hcq0 hcq4)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1828 A.natDegree B.natDegree F.natDegree hcq7 h)
      · exact Or.inr (astra4u_Round4Package_nat_1829 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2042 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1831 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1832 A.natDegree B.natDegree E.natDegree F.natDegree hcq5 h hcq7 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_2043 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 hcq7 hcq0 hcq4 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2863 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq5 hcq7 hcq0 hcq4)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq1 hcq5 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq1 hcq2 hcq7; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq1 hcq5 hcq7; omega) (by clear * - hcq4 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq5 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hcq0 hcq2 hcq4 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEF24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq3 hcq4 hcq7 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1404 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1835 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq3 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2045 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1405 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1406 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2864 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq3 hcq1 h hcq0 hcq10 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1408 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1837 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq3 hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_2047 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq1 h hcq10 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1409 A.natDegree B.natDegree E.natDegree F.natDegree hcq1 h hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1410 A.natDegree B.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq10)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2865 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq3 hcq1 hcq0 hcq10 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq10; omega) (by clear * - hcq1 hcq6 hcq10; omega) (by clear * - hcq1 hcq3 hcq10; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq1 hcq3 hcq10; omega) (by clear * - hcq0 hcq1 hcq6 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1412 A.natDegree B.natDegree E.natDegree F.natDegree h hcq0 hcq5 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq0 hcq7)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2866 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq1 hcq5 h hcq7 hcq4)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq7 hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1414 A.natDegree B.natDegree E.natDegree F.natDegree hcq0 hcq5 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2867 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq0 hcq1 hcq5 h hcq7 hcq4)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq5 hcq7; omega) (by clear * - hcq1 hcq4 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq4; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) (Or.inr (by clear * - hcq0 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCDEF26810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF26810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAB hGn hcq0 hcq7 hcq8 hApos hcq15 hcq16 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1719 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq8 hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1720 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq8 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1721 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hAC h hcq8 hcq2 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2868 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAC hcq8 hcq2 hcq1 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1722 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hAC hcq2 hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2869 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hAC h hcq8 hcq2 hcq16)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0571 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_0572 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1190 A.natDegree B.natDegree C.natDegree D.natDegree hAC h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0574 A.natDegree B.natDegree C.natDegree E.natDegree h hcq8 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1245 A.natDegree B.natDegree C.natDegree F.natDegree h hAC hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1068 A.natDegree G.natDegree hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2870 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq8 hcq2 hcq1 hcq16)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_0578 A.natDegree B.natDegree C.natDegree hcq8 h)
      · exact Or.inr (astra4u_Round4Package_nat_0579 A.natDegree B.natDegree C.natDegree h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1192 A.natDegree B.natDegree C.natDegree D.natDegree hApos h hcq8 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_0581 A.natDegree B.natDegree C.natDegree E.natDegree h hcq8 hcq16)
      · exact Or.inr (astra4u_Round4Package_nat_1247 A.natDegree B.natDegree C.natDegree F.natDegree hAC h hcq1 hcq0)
      · exact absurd h (astra4u_Round4Package_nat_1070 A.natDegree G.natDegree hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1725 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq8 hcq2 hcq0)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq8; omega) (by clear * - hAC hcq8; omega) (by clear * - hcq0; omega) (by clear * - hcq2; omega) (by clear * - hcq8 hcq16; omega) (by clear * - hAC hcq2 hcq8; omega) (by clear * - hAC hcq1 hcq2; omega) (by clear * - hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq2 hcq8 hApos; omega)) hbdelta' (Or.inr (by clear * - hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega)) (Or.inr (by clear * - hcq8 hApos; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·CCC` dies on the `μ` face `3 * C.natDegree`. -/
theorem quarticChamberBCDEF28810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF28810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 3 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq4 hcq5 hcq7 hApos hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree ∧ D.natDegree + E.natDegree < 3 * C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + F.natDegree < 3 * C.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1726 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1727 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1728 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2871 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq12 hcq15 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1729 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq7 hcq0 hcq12 hcq15)
      · exact absurd h (astra4u_Round4Package_nat_1254 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq7 hcq12 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2872 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq12 hcq15 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + F.natDegree < 3 * C.natDegree ∧ B.natDegree + E.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1256 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1257 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1731 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1846 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq12 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1260 A.natDegree B.natDegree C.natDegree F.natDegree h hcq7 hcq0 hcq12)
      · exact absurd h (astra4u_Round4Package_nat_1261 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq7 hcq12 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2873 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq2 hcq12 hcq15 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree ∧ F.natDegree < 3 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1263 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1264 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1733 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq12 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_1848 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq12 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1267 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq12)
      · exact absurd h (astra4u_Round4Package_nat_1268 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree hcq7 hcq12 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1734 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq0 hcq2 hcq12 hcq15)
  have hrest : (muQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq7 hcq12; omega) (by clear * - hcq0 hcq12; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq6 hcq12; omega) (by clear * - hcq0 hcq12 hcq15; omega) (by clear * - hcq0 hcq15; omega) (by clear * - hcq0 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hApos hcq12 hcq15; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq6 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hApos hcq12 hcq15; omega)) (Or.inr (by clear * - hcq0 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hApos hcq12; omega))
  have hlead : (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree :=
    muQuarticChamberFace0810_natDegree A B C D E F G hCne
  rw [degreeZeroMuQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberBCDEF29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF29810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1735 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1736 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq14 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1737 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 hcq14 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2874 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq3 hcq14 hcq11 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1739 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq14 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1740 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq3 hcq14 hcq1 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2875 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq14 hcq1 hcq11 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1742 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1743 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1744 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2876 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq11 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1746 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1747 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq3 hcq14 hcq1 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2877 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq14 hcq11 hcq2)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1749 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq1 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1750 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1751 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2878 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq3 h hcq11 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1753 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 hcq3 h hcq11)
      · exact absurd h (astra4u_Round4Package_nat_1754 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq3 hcq14 hcq1 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2539 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq1 hcq11)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq11; omega) (by clear * - hcq0 hcq3 hcq11; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq11; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEF31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF31810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2879 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq6 hcq2 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2205 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2206 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq15)
      · exact Or.inr (astra4u_Round4Package_nat_2207 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq2 hcq15 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2208 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq15)
      · exact absurd h (astra4u_Round4Package_nat_2880 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq0 hcq6 hcq2 hcq15 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2881 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq6 hcq2 hcq15 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq0 hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq1 hcq2 hcq6 hcq15; omega) (by clear * - hcq0 hcq2 hcq15; omega) (by clear * - hcq0 hcq6 hcq15; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq15; omega) (by clear * - hcq6 hcq15; omega) (by clear * - hcq2 hcq6 hcq15; omega) (by clear * - hcq2 hcq15; omega) (by clear * - hcq0 hcq1 hcq6 hcq15; omega) (by clear * - hcq15; omega) (by clear * - hcq0 hcq1 hcq2 hcq15; omega) (by clear * - hcq1 hcq15; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq15; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·DD·DE·EE` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEF32810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF32810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2882 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2216 A.natDegree C.natDegree D.natDegree F.natDegree hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_2217 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2218 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2219 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2220 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq1 hcq5 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2883 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq14 hcq3 hcq11 hcq1 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2884 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq3 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2223 A.natDegree C.natDegree D.natDegree F.natDegree hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_2224 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2225 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2226 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2227 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq1 hcq5 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2885 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq14 hcq3 hcq11 hcq1 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2886 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq3 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2230 A.natDegree C.natDegree D.natDegree F.natDegree h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2231 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2232 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2233 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq14 h hcq1 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_2234 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq14 hcq1 hcq5 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2887 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq14 hcq3 hcq11 hcq1 hcq5)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq3 hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega) (by clear * - hcq1 hcq5 hcq11; omega) (by clear * - hcq1 hcq5 hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq1 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEF35810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF35810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq2 hcq4 hcq5 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2888 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2889 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2890 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2891 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2892 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1543 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq0 hcq5 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2893 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ 3 * B.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ B.natDegree + E.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1854 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1855 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2894 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1856 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1857 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1550 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq0 hcq5 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2895 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq11 hcq3 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ A.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + C.natDegree < 2 * E.natDegree ∧ F.natDegree < 2 * E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 2 * E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1859 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 hcq0 h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1860 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2896 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1862 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1863 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq5)
      · exact absurd h (astra4u_Round4Package_nat_1864 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hcq14 hcq1 hcq0 hcq5 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2897 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq0 hcq11 hcq3 hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq3 hcq5 hcq11; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq11; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberBCDEF37810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF37810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq3 hcq4 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < 2 * E.natDegree ∧ 3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1866 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq3 hcq0 hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1551 A.natDegree C.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2245 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq14 h hcq0 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1552 A.natDegree C.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1553 A.natDegree C.natDegree E.natDegree F.natDegree h hcq14 hcq0 hcq1)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2898 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq14 hcq3 hcq0 hcq1 hcq11 hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq0 hcq3 hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq1 hcq3 hcq11; omega) (by clear * - hcq0 hcq1 hcq5 hcq11; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq1 hcq5; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEF38810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF38810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hdpos : 0 < 2 * F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq2 hcq5 hcq7 hcq8 hcq11 hcq14 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1270 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1147 A.natDegree C.natDegree F.natDegree hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_1519 A.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq14 h)
      · exact Or.inr (astra4u_Round4Package_nat_1558 A.natDegree C.natDegree E.natDegree F.natDegree h hcq14 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1148 A.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact absurd h (astra4u_Round4Package_nat_1067 A.natDegree G.natDegree hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2899 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 hcq0 h hcq14 hcq1 hcq11 hcq6)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hGz (by clear * - hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq6 hcq11; omega) (by clear * - hcq0 hcq4 hcq11; omega) (by clear * - hcq1 hcq4 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq4; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq4 hcq6 hcq11; omega) (by clear * - hcq0 hcq6 hcq14; omega) (by clear * - hcq0 hcq4 hcq14; omega) hbl' (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
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
/-- Chamber `BCDEFG` / `BF·BG·CF·CG·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2467 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2468 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2469 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2900 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq1 hcq14 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2471 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2472 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq14 hcq3 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2901 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq14 hcq3 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2474 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2475 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2476 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2902 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq14 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2478 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2479 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq14 hcq3 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2903 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq14 hcq3 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2481 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq1 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2482 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2483 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2904 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq1 hcq14 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2485 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq3 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2486 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq14 hcq3 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2905 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq1 hcq14 hcq3 hcq5)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq3 hcq5 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq3 hcq5 hcq14; omega) (by clear * - hcq3 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega) (by clear * - hcq3 hcq5 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq5 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq5 hcq14; omega) (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq3 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq5 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hcq5 hcq14; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq5 hcq14; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·BG·CF·CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG14810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hcq8 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2906 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2907 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2908 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2909 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2910 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2911 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq14 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2912 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + 3 * B.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2913 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2914 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2915 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2916 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2917 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2918 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq14 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2919 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq14 hcq9)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < E.natDegree + G.natDegree ∧ 3 * B.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ B.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2920 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq1 hcq0 hcq3 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2921 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2922 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2923 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2924 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 h hcq1 hcq0 hcq3 hcq14 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_2925 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq4 hcq1 hcq0 hcq3 hcq14 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2926 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq3 hcq14 hcq9)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq3 hcq9 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq3 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9 hcq14; omega) (by clear * - hcq0 hcq3 hcq9 hcq14; omega) (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq0 hcq1 hcq3 hcq9 hcq14; omega) (by clear * - hcq0 hcq3 hcq9 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq3 hcq4 hcq9 hcq14; omega) (by clear * - hcq0 hcq3 hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq9 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq9 hcq14; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·BG·CF·CG·FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG17810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq6 hcq10 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1803 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1804 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2488 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2601 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq14 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1930 A.natDegree B.natDegree C.natDegree F.natDegree h hcq3 hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1931 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq0 hcq14)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2927 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq0 hcq14 hcq8 hcq12)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1808 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1809 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2490 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq14 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2603 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq14 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1933 A.natDegree B.natDegree C.natDegree F.natDegree h hcq3 hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1934 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq3 hcq1 hcq0 hcq14)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2928 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq3 h hcq1 hcq0 hcq14 hcq8 hcq12)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq12 hcq14; omega) (by clear * - hcq3 hcq8 hcq14; omega) (by clear * - hcq1 hcq8 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq3 hcq8; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq8 hcq12 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq12 hcq14; omega) (by clear * - hcq3 hcq8 hcq14; omega) (by clear * - hcq3 hcq12; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hApos hcq12 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hApos hcq12 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos hcq12; omega)) (Or.inr (by clear * - hcq3 hcq8 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·BG·FF·FG·GG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG27810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1098 A.natDegree B.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1913 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2150 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1119 A.natDegree B.natDegree F.natDegree h hcq1 hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1471 A.natDegree B.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2929 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hcq0 hcq13 hcq5 hcq8 hcq12)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1121 A.natDegree B.natDegree F.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_1915 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2152 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_1122 A.natDegree B.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1473 A.natDegree B.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2930 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq0 hcq13 hcq5 hcq8 hcq12)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq5 hcq13; omega) (by clear * - hcq1 hcq13; omega) (by clear * - hcq1 hcq8; omega) (by clear * - hcq0 hcq12 hcq13; omega) (by clear * - hcq0 hcq5 hcq8 hcq13; omega) (by clear * - hcq0 hcq5 hcq13; omega) (by clear * - hcq5; omega) (by clear * - hcq8; omega) (by clear * - hcq0 hcq1 hcq12; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·CF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG28810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG28810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1674 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1798 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq7 hcq0 hcq14 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1218 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1938 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq2 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2931 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq0 hcq14 hcq2 hcq5 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1676 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1800 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq14 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1225 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1940 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq2 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2830 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq14 hcq5 hcq10)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1228 A.natDegree B.natDegree C.natDegree F.natDegree hcq0 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1229 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1678 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1802 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq7 h hcq0 hcq14 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1232 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1941 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq2 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1679 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq14 hcq5 hcq10)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq14; omega) (by clear * - hcq0 hcq10 hcq14; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq7 hcq10 hcq14; omega) (by clear * - hcq5 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq2; omega) (by clear * - hcq5; omega) (by clear * - hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq10 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq7 hcq10 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq10 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq10 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq10 hcq14; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·CF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEFG32810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG32810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1680 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1681 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1682 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2831 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq3 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1683 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2495 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq14 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2932 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq3 hcq14 hcq1 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1685 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1686 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1687 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2833 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq3 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1688 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq3 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2497 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq14 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2834 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq3 hcq14 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq0 hcq8 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega) (by clear * - hcq0 hcq3 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq3 hcq8 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq14; omega) (by clear * - hcq8 hcq14; omega) (by clear * - hcq3 hcq14; omega) (by clear * - hcq1 hcq2 hcq14; omega) (by clear * - hcq0 hcq2 hcq3 hcq14; omega) (by clear * - hcq0 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·CF·DD·DE·EE` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG33810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG33810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2467 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2468 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2469 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2835 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq14 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2471 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2933 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq1 hcq5 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2934 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq14 hcq1 hcq5 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2474 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2475 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2476 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2838 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq14 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2478 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2935 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq1 hcq5 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2840 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq14 hcq1 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2481 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq0 h hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2482 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2483 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2841 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq14 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2485 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2936 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq14 hcq1 hcq5 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2843 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq14 hcq1 hcq6)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq6 hcq14; omega) (by clear * - hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq6 hcq14; omega) (by clear * - hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq6 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq5; omega) (by clear * - hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq14; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq14; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·CF·DD·DF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEFG35810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG35810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1680 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1681 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1682 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2844 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hcq0 hcq2 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1683 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2495 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq2 hcq14 hcq1 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2937 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq6 h hcq0 hcq2 hcq14 hcq1 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1685 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1686 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1687 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2846 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq2 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1688 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq14 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2497 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq2 hcq14 hcq1 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2847 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq6 h hcq0 hcq2 hcq14 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq0 hcq5 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq6 hcq14; omega) (by clear * - hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq0 hcq2 hcq14; omega) (by clear * - hcq2 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq2 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq6 hcq14; omega) (by clear * - hcq5 hcq14; omega) (by clear * - hcq2 hcq14; omega) (by clear * - hcq1 hcq6 hcq14; omega) (by clear * - hcq0 hcq2 hcq6 hcq14; omega) (by clear * - hcq0 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·CF·EE·EF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberBCDEFG38810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG38810 A B C D E F G)
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
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq4 hcq6 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1803 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1804 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2488 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1805 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1806 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2608 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hcq14 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2938 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 h hcq0 hcq1 hcq14 hcq5 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1808 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1809 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2490 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1810 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq2 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1811 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_2609 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq2 hcq0 hcq1 hcq14 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2849 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq0 hcq1 hcq14 hcq8)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq1 hcq2 hcq8 hcq14; omega) (by clear * - hcq0 hcq8 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq2 hcq8; omega) (by clear * - hcq0 hcq5 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq8 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq14; omega) (by clear * - hcq1 hcq2 hcq8 hcq14; omega) (by clear * - hcq0 hcq1 hcq2 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq8 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·CF·FF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG39810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG39810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1214 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1215 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1674 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1813 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree h hcq1 hcq8 hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1235 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1942 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq14 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2939 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq8 h hcq0 hcq14 hcq3 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1221 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1222 A.natDegree B.natDegree C.natDegree F.natDegree h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1676 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq14 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1815 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq1 hcq8 h hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1237 A.natDegree B.natDegree C.natDegree F.natDegree h hcq1 hcq0 hcq14)
      · exact Or.inr (astra4u_Round4Package_nat_1944 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq1 hcq0 hcq14 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2851 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq8 h hcq0 hcq14 hcq6)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq8 hcq14; omega) (by clear * - hcq6 hcq14; omega) (by clear * - hcq0 hcq14; omega) (by clear * - hcq3; omega) (by clear * - hcq6; omega) (by clear * - hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG40810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG40810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1692 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1693 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1694 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2011 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq4 hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1696 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2121 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2940 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq2 hcq4 hcq1 h hcq13 hcq0 hcq5)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1699 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1700 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1701 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2014 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1703 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2123 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2853 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 hcq4 h hcq13 hcq0 hcq5)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1706 A.natDegree B.natDegree D.natDegree F.natDegree hcq13 h)
      · exact Or.inr (astra4u_Round4Package_nat_1707 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree hcq2 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1708 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2017 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree hcq4 h hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1710 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2125 A.natDegree B.natDegree D.natDegree F.natDegree G.natDegree h hcq1 hcq13 hcq0 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2854 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq2 hcq4 hcq13 hcq0 hcq5)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq5 hcq13; omega) (by clear * - hcq0 hcq4 hcq13; omega) (by clear * - hcq2 hcq13; omega) (by clear * - hcq0 hcq5 hcq13; omega) (by clear * - hcq0 hcq2 hcq5 hcq13; omega) (by clear * - hcq0 hcq1 hcq5 hcq13; omega) (by clear * - hcq0 hcq2 hcq5 hcq13; omega) (by clear * - hcq0 hcq4 hcq5 hcq13; omega) (by clear * - hcq0 hcq2 hcq4 hcq13; omega) (by clear * - hcq2 hcq5 hcq13; omega) (by clear * - hcq0 hcq1 hcq4; omega) (by clear * - hcq0 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq4 hcq5 hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq5 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq5 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq13; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberBCDEFG42810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG42810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2019 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2855 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2020 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2021 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2022 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2681 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq2 hcq16 hcq0 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2941 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq7 h hcq1 hcq2 hcq16 hcq0 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_2024 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2857 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2025 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2026 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2027 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree h hcq1 hcq2 hcq16 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2683 A.natDegree B.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq2 hcq16 hcq0 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2858 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq7 h hcq1 hcq2 hcq16 hcq0)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq2 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq10 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq2 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq1 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq1 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq10 hcq16; omega) (by clear * - hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq7 hcq10 hcq16; omega) (by clear * - hcq0 hcq1 hcq7 hcq16; omega) (by clear * - hcq1 hcq2 hcq7 hcq16; omega) (by clear * - hcq0 hcq16; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos hcq16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos hcq16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos hcq16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos hcq16; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi

end QuarticChamberKills810

end Max11DegreeRoutes
