import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart04Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart05Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart06Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart07Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart08Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart09Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart10Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart11Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart12Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart13Scratch
import Grok810ScaleZeroQuarticChamberKills4Part101SpeedTPart14Scratch
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
/-- Chamber `CDEFG` / `CF·DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDEFG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG17810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2205 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2206 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2207 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq2 hcq12 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2208 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2727 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq2 hcq12 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2728 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hcq2 hcq12 hcq1 hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2210 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2211 A.natDegree C.natDegree D.natDegree F.natDegree h hcq2 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2212 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq2 hcq12 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2213 A.natDegree C.natDegree D.natDegree F.natDegree h hcq0 hcq2 hcq12)
      · exact Or.inr (astra4u_Round4Package_nat_2729 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq2 hcq12 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2214 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq2 hcq12 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq2 hcq12; omega) (by clear * - hcq2 hcq12; omega) (by clear * - hcq2 hcq7 hcq12; omega) (by clear * - hcq12; omega) (by clear * - hcq0 hcq1 hcq2 hcq12; omega) (by clear * - hcq1 hcq12; omega) (by clear * - hcq2 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace2810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·DD·DE·EE` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberCDEFG18810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG18810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2215 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq11 hBn hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2216 A.natDegree C.natDegree D.natDegree F.natDegree hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_2217 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq11 h hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2218 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq11 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2219 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2730 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq11 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2731 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 hcq3 h hcq11 hcq1 hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2222 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq11 hBn hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2223 A.natDegree C.natDegree D.natDegree F.natDegree hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_2224 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq11 h hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2225 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2226 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2732 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq11 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2228 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 h hcq11 hcq1 hcq6)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2229 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq11 hBn hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2230 A.natDegree C.natDegree D.natDegree F.natDegree h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_2231 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq11 h hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2232 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2233 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq0 hcq11 h hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2733 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq3 hcq11 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2235 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq0 hcq11 hcq1 hcq6)
  have hrest : (xiQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest15810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq1 hcq11; omega) (by clear * - hcq0 hcq1 hcq6 hcq11; omega) (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq1 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq11; omega))
  have hlead : (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace15810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face15_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEFG21810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG21810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq4 hcq6 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1538 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq11 hcq0 hBn hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2236 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq3 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2237 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq3 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2238 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq11 hcq0 hcq3 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2239 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq11 hcq0 hcq3 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_2734 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq11 hcq0 hcq3 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2240 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq11 hcq0 hcq6)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_1545 A.natDegree B.natDegree C.natDegree E.natDegree F.natDegree hcq11 hcq0 hBn hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_2241 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq3 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_2242 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq3 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_2243 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq3 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_2244 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq11 hcq0 hcq3 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_2735 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq11 hcq0 hcq3 hcq6)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq3 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq6 hcq11; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEFG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq3 hcq4 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1551 A.natDegree C.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2245 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1552 A.natDegree C.natDegree E.natDegree F.natDegree h hcq11 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1553 A.natDegree C.natDegree E.natDegree F.natDegree h hcq11 hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2346 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq0 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2246 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq11 hcq0 hcq1 hcq5)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1555 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2247 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq11 h hcq0 hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1556 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1557 A.natDegree C.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2347 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq0 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2248 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq0 hcq1 h hcq5)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq5; omega) (by clear * - hcq0 hcq11; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq5; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDEFG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG24810 A B C D E F G)
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
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq6 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1147 A.natDegree C.natDegree F.natDegree hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_1519 A.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_1558 A.natDegree C.natDegree E.natDegree F.natDegree h hcq11 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1148 A.natDegree C.natDegree F.natDegree h hcq0 hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1578 A.natDegree C.natDegree F.natDegree G.natDegree h hcq11 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2736 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq4 hcq0 h hcq11 hcq7 hcq9)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1150 A.natDegree C.natDegree F.natDegree hApos hcq0 h)
      · exact Or.inr (astra4u_Round4Package_nat_1521 A.natDegree C.natDegree D.natDegree F.natDegree hcq4 hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_1560 A.natDegree C.natDegree E.natDegree F.natDegree hcq11 h hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1579 A.natDegree C.natDegree F.natDegree G.natDegree h hcq11 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2250 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq4 hcq0 hcq7)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq4; omega) (by clear * - hcq0 hcq7 hcq11; omega) (by clear * - hcq0 hcq4 hcq11; omega) (by clear * - hcq0 hcq7 hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq7 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEFG27810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG27810 A B C D E F G)
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
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq3 hcq4 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2737 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 hBn hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2738 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2739 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2740 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq2 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2741 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2742 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq0 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2743 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq2 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2744 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 hBn hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2745 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2746 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2747 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq2 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2748 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2749 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq0 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2750 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq2 hcq0)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ C.natDegree + F.natDegree < 2 * G.natDegree ∧ D.natDegree + E.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2751 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 hBn hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2752 A.natDegree C.natDegree F.natDegree G.natDegree hcq11 h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2753 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2754 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq2 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2755 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 hcq4 h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2756 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq0 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2757 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq2 hcq0)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq1; omega) (by clear * - hcq11; omega) (by clear * - hcq3 hcq11; omega) (by clear * - hcq0 hcq2 hcq11; omega) (by clear * - hcq2 hcq4 hcq11; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hApos hcq11; omega)) (Or.inr (by clear * - hcq11; omega)) (Or.inr (by clear * - hcq1 hApos hcq11; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CG·DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEFG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG29810 A B C D E F G)
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
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hcq6 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2287 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq11 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2288 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq11 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2289 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq11 hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2758 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq11 hcq2 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2290 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq11 hcq2 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2759 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq11 h hcq2 hcq0 hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2292 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq11 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2293 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq11 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2294 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hcq11 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2760 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hcq11 hcq2 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2295 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hcq11 hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2761 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq11 h hcq2 hcq0 hcq7)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq1 hcq2 hcq7; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq1 hcq2 hcq11; omega) (by clear * - hcq1 hcq2 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CG·DD·DG·GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEFG32810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG32810 A B C D E F G)
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
    exact hnc (by clear * - hBn hcq0 hcq1 hcq3 hcq4 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2327 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2328 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2762 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq1 hcq5 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2329 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq1 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2330 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq1 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2763 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq11 h hcq1 hcq0 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2332 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2333 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hcq11 h hcq1 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2764 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq1 hcq5 hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_2334 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq1 hcq0 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2335 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq11 hcq1 hcq0 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2765 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq11 h hcq1 hcq0 hcq5 hcq8)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq1 hcq5; omega) (by clear * - hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq0 hcq1 hcq8 hcq11; omega) (by clear * - hcq0 hcq8 hcq11; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEFG33810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG33810 A B C D E F G)
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
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq5 hcq6 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2766 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq11 hcq2 hBn hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2767 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2768 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2769 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2770 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2771 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq2 hcq1 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2772 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq0 hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2773 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq11 hcq2 hBn hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2774 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2775 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2776 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2777 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2778 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq2 hcq1 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2779 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq0 hcq7)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2780 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq11 hcq2 hBn hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2442 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq11 h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2443 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq11 h hcq2 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2444 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq11 h hcq2 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2781 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq2 hcq1 hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_2446 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq11 hcq2 hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2782 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq1 hcq0 hcq7)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq2 hcq7 hcq11; omega) (by clear * - hcq0 hcq1 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq11; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEFG35810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG35810 A B C D E F G)
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
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq3 hcq4 hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2783 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2784 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2785 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2786 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2787 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq3 hcq1 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2788 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq1 hcq0)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2789 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2790 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2791 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq11 h hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2792 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq3 hcq1 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2793 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq11 hcq4 hcq3 hcq1 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2794 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq4 hcq3 hcq1 hcq0)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq3 hcq4; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq1 hcq4 hcq11; omega) (by clear * - hcq0 hcq1 hcq3; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `DD` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDEFG37810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG37810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1132 A.natDegree C.natDegree D.natDegree hcq11 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1156 A.natDegree D.natDegree E.natDegree h hcq2 hAD)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1529 A.natDegree D.natDegree G.natDegree h hcq4 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2251 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq2 h hcq11 hAD hcq3)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1134 A.natDegree C.natDegree D.natDegree hApos hcq11 h)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1158 A.natDegree D.natDegree E.natDegree hcq2 hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1167 A.natDegree D.natDegree F.natDegree h hAD hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1530 A.natDegree D.natDegree G.natDegree h hcq4 hAD)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1524 A.natDegree C.natDegree D.natDegree F.natDegree hApos h hcq11 hcq3)
  have hbdelta' : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_1047 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1136 A.natDegree C.natDegree D.natDegree hApos h hcq11)
      · exact Or.inr (astra4u_Round4Package_nat_1069 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1159 A.natDegree D.natDegree E.natDegree hApos hcq2 h)
      · exact Or.inr (astra4u_Round4Package_nat_1169 A.natDegree D.natDegree F.natDegree hAD h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1531 A.natDegree D.natDegree G.natDegree hApos h hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1170 A.natDegree D.natDegree F.natDegree h hcq3)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq11; omega) (by clear * - hcq1; omega) (by clear * - hcq3; omega) (by clear * - hcq2; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq11; omega)) hbdelta' (Or.inr (by clear * - hcq2 hcq11; omega)) (Or.inr (by clear * - hcq3; omega)) (Or.inr (by clear * - hcq11; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `DD·DE·DF·EE·EF·FF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDEFG40810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG40810 A B C D E F G)
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
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2252 A.natDegree C.natDegree D.natDegree F.natDegree hcq5 hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1591 A.natDegree D.natDegree F.natDegree hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1592 A.natDegree D.natDegree E.natDegree F.natDegree h hAD hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1593 A.natDegree D.natDegree F.natDegree h hAD hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_2372 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2795 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq5 h hAD hcq0 hcq1 hcq8)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2254 A.natDegree C.natDegree D.natDegree F.natDegree hcq5 hAD h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1595 A.natDegree D.natDegree F.natDegree hApos h hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1596 A.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq1)
      · exact Or.inr (astra4u_Round4Package_nat_1353 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_2374 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAD hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2255 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq5 h hAD hcq0 hcq1)
  have hrest : (piQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5 hcq8; omega) (by clear * - hAD hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1 hcq5; omega) (by clear * - hAD hcq0 hcq1; omega) (by clear * - hcq0 hcq1 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hAD hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq8 hApos; omega)) (Or.inr (by clear * - hcq1 hcq5 hApos; omega))
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
/-- Chamber `CDEFG` / `DD·DE·DG·EE·EG·GG` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEFG41810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG41810 A B C D E F G)
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
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hcq0 hcq1 hcq6 hcq7 hcq11 hcq12 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2307 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1614 A.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1615 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2376 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1616 A.natDegree D.natDegree E.natDegree G.natDegree h hcq1 hAD hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2796 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 h hAD hcq0 hcq6 hcq7)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2309 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree hcq1 hAD h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1618 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1619 A.natDegree D.natDegree E.natDegree G.natDegree hApos hcq1 h)
      · exact Or.inr (astra4u_Round4Package_nat_2378 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq1 hAD hcq0 hcq7)
      · exact Or.inr (astra4u_Round4Package_nat_1620 A.natDegree D.natDegree E.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2797 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 h hcq0 hcq6 hcq7)
  have hrest : (xiQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest12810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq1 hcq7; omega) (by clear * - hAD hcq1 hcq6; omega) (by clear * - hAD hcq0 hcq1 hcq6; omega) (by clear * - hcq0 hcq1 hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega))
  have hlead : (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace12810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face12_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `DD·DG·GG` dies on the `μ` face `A.natDegree + 2 * D.natDegree`. -/
theorem quarticChamberCDEFG46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG46810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  have hdpos : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0845 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0846 A.natDegree D.natDegree hAD h)
      · exact Or.inr (astra4u_Round4Package_nat_1054 A.natDegree D.natDegree E.natDegree G.natDegree h hcq0 hAD hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1165 A.natDegree D.natDegree F.natDegree h hAD hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0848 A.natDegree D.natDegree G.natDegree h hcq0 hAD)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2798 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq0 h hAD hcq3 hcq8 hcq5)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_0851 A.natDegree C.natDegree D.natDegree G.natDegree hcq0 hAD h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_0852 A.natDegree D.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1056 A.natDegree D.natDegree E.natDegree G.natDegree hcq0 hAD h hcq8)
      · exact Or.inr (astra4u_Round4Package_nat_1167 A.natDegree D.natDegree F.natDegree h hAD hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_0854 A.natDegree D.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2338 A.natDegree C.natDegree D.natDegree F.natDegree G.natDegree hApos h hcq0 hcq3 hcq5)
  have hrest : (muQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest1810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hAD hcq0 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq5; omega) (by clear * - hcq0 hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree :=
    muQuarticChamberFace1810_natDegree A B C D E F G hAne hDne
  rw [degreeZeroMuQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `EE` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEFG47810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG47810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hcq0 hcq2 hcq6 hcq7 hcq11 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2256 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq6 h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2257 A.natDegree D.natDegree E.natDegree F.natDegree hcq6 hAE h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2258 A.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hAE hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2259 A.natDegree D.natDegree E.natDegree F.natDegree h hcq6 hAE hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_2799 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq6 hAE hcq2 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2260 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 h hAE)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_2261 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq13 hcq6 h hcq2)
    · exact Or.inr (astra4u_Round4Package_nat_2262 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq6 hAE h hcq2)
    · exact Or.inr (astra4u_Round4Package_nat_2263 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq13 hcq6 h hcq2)
    · exact Or.inr (astra4u_Round4Package_nat_2264 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq13 hcq6 hAE hcq4)
    · exact Or.inr (astra4u_Round4Package_nat_2800 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq13 hcq6 hAE hcq2 hcq7)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq2; omega) (by clear * - hcq11; omega) (by clear * - hcq1; omega) (by clear * - hcq4; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq2 hApos hcq11; omega)) (Or.inr (by clear * - hcq2 hcq6; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos; omega)) (Or.inr (by clear * - hcq2 hApos hcq11; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCDEFG48810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG48810 A B C D E F G)
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
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq7 hcq8 hcq12 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2265 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq13 hcq0 hcq3 hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2266 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq0 h hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2267 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq0 h hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2268 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq13 hcq0 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2269 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq13 hcq0 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2801 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq13 hcq0 hcq1 hcq3 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2802 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq13 hcq0 h hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2272 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq13 hcq0 hcq3 hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2273 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq0 h hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2274 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq0 h hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2275 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq0 h hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2276 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq13 hcq0 hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2803 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq13 hcq0 hcq1 hcq3 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2278 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq0 h)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_2279 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree hcq13 hcq0 hcq3 hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1665 A.natDegree C.natDegree D.natDegree E.natDegree h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1666 A.natDegree C.natDegree D.natDegree E.natDegree hcq13 hcq0 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1667 A.natDegree C.natDegree D.natDegree E.natDegree hcq13 hcq0 h hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2280 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq13 hcq0 h hcq1 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2460 A.natDegree C.natDegree D.natDegree E.natDegree G.natDegree h hcq13 hcq0 hcq3 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2282 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hcq13 hcq0 hcq1)
  have hrest : (xiQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq3 hcq13; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq13; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq13; omega))
  have hlead : (xiQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace2810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `EE·EF·EG·FF·FG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEFG49810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG49810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hcq0 hcq1 hcq5 hcq7 hcq11 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2360 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq0 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1608 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2180 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2804 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq1 hcq6 hcq9)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2362 A.natDegree C.natDegree E.natDegree F.natDegree G.natDegree hAE h hcq0 hcq1 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1610 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1571 A.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1572 A.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2363 A.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2805 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq0 hcq1 h hcq6 hcq9)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq9; omega) (by clear * - hAE hcq1 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq9; omega) hbl' hbbeta' (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq9 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq9 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `EE·EF·FF` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEFG50810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG50810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hcq0 hcq2 hcq4 hcq8 hcq11 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1568 A.natDegree C.natDegree E.natDegree F.natDegree hAE h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1608 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1425 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1426 A.natDegree E.natDegree F.natDegree h hAE hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2182 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2283 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree h hAE hcq2 hcq0 hcq6)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    have hbbetas : beta = 0 ∨ (A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1570 A.natDegree C.natDegree E.natDegree F.natDegree hAE h hcq2 hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1610 A.natDegree D.natDegree E.natDegree F.natDegree hAE h hcq0 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1571 A.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_1572 A.natDegree E.natDegree F.natDegree hApos h hcq0)
      · exact Or.inr (astra4u_Round4Package_nat_2364 A.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2284 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos hcq2 hcq0 h hcq6)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq6; omega) (by clear * - hAE hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `EE·EG·GG` dies on the `μ` face `2 * E.natDegree`. -/
theorem quarticChamberCDEFG51810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG51810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hAD hBn hcq0 hcq2 hcq3 hcq4 hcq8 hcq11 hcq13 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧ C.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_2806 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hAE h hcq4 hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_2257 A.natDegree D.natDegree E.natDegree F.natDegree hcq8 hAE h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2258 A.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hAE hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2259 A.natDegree D.natDegree E.natDegree F.natDegree h hcq8 hAE hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_2807 A.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hAE hcq4 hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2808 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAE hcq0 hcq3)
  have hbbeta' : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree ∧ C.natDegree + D.natDegree < 2 * E.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
    · exact Or.inr (astra4u_Round4Package_nat_2809 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hAE h hcq4 hcq0 hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_2810 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq8 hAE h hcq4 hcq0 hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_2811 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq8 h hcq4 hcq0 hcq3)
    · exact Or.inr (astra4u_Round4Package_nat_2812 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq8 hAE hcq0 hcq3 hcq6)
    · exact Or.inr (astra4u_Round4Package_nat_2813 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq8 hcq4 hcq0 hcq3)
  have hrest : (muQuarticChamberRest2810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * E.natDegree :=
    muQuarticChamberRest2810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq4; omega) (by clear * - hAE hcq0 hcq3; omega) (by clear * - hcq3; omega) (by clear * - hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega))
  have hlead : (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree :=
    muQuarticChamberFace2810_natDegree A B C D E F G hEne
  rw [degreeZeroMuQuartic810_eq_face2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `FF` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDEFG52810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG52810 A B C D E F G)
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
    exact hnc (by clear * - hAC hAD hAE hBn hcq0 hcq2 hcq6 hcq9 hApos hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1152 A.natDegree C.natDegree F.natDegree hcq0 hAF h)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1175 A.natDegree E.natDegree F.natDegree h hAF hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1481 A.natDegree F.natDegree G.natDegree h hcq9 hAF)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2814 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq9 hcq0 h hAF hcq6 hcq2)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1154 A.natDegree C.natDegree F.natDegree hcq0 h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1173 A.natDegree D.natDegree F.natDegree hAF h hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1177 A.natDegree E.natDegree F.natDegree hAF h hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1580 A.natDegree F.natDegree G.natDegree h hcq9 hAF)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2286 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hApos h hcq0 hcq6 hcq2)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq2; omega) (by clear * - hAF hcq0 hcq6; omega) (by clear * - hAF hcq0 hcq2; omega) (by clear * - hcq8; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `FF·FG·GG` dies on the `ξ` face `2 * F.natDegree`. -/
theorem quarticChamberCDEFG53810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG53810 A B C D E F G)
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
    exact hnc (by clear * - hAC hAD hAE hBn hcq0 hcq2 hcq4 hcq8 hApos hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * F.natDegree ∧ D.natDegree + G.natDegree < 2 * F.natDegree ∧ E.natDegree + F.natDegree < 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1581 A.natDegree C.natDegree F.natDegree G.natDegree hAF h hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1171 A.natDegree D.natDegree F.natDegree hAF h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1631 A.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1071 A.natDegree F.natDegree h hAF)
      · exact Or.inr (astra4u_Round4Package_nat_1482 A.natDegree F.natDegree G.natDegree h hAF hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2815 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hAF hcq0 hcq3 hcq4 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧ C.natDegree + F.natDegree < 2 * F.natDegree ∧ D.natDegree + E.natDegree < 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1583 A.natDegree C.natDegree F.natDegree G.natDegree h hAF hcq0 hcq3)
      · exact Or.inr (astra4u_Round4Package_nat_1173 A.natDegree D.natDegree F.natDegree hAF h hcq4)
      · exact Or.inr (astra4u_Round4Package_nat_1633 A.natDegree E.natDegree F.natDegree G.natDegree hAF h hcq0 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1072 A.natDegree F.natDegree hApos h)
      · exact Or.inr (astra4u_Round4Package_nat_1584 A.natDegree F.natDegree G.natDegree hApos h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2816 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos h hcq0 hcq3 hcq4 hcq10)
  have hrest : (xiQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * F.natDegree :=
    xiQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq4; omega) (by clear * - hAF hcq0 hcq3 hcq10; omega) (by clear * - hAF hcq0 hcq3 hcq4; omega) (by clear * - hcq10; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hApos hcq10; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega))
  have hlead : (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree :=
    xiQuarticChamberFace0810_natDegree A B C D E F G hFne
  rw [degreeZeroXiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  exact (Nat.ne_of_gt hdpos) hxi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `GG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEFG54810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG54810 A B C D E F G)
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
    exact hnc (by clear * - hAC hAD hAE hAF hBn hcq1 hcq2 hcq6 hcq9 hApos hcq11 hzero; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0844 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1586 A.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1627 A.natDegree D.natDegree F.natDegree G.natDegree hcq4 hcq2 hAG h)
      · exact Or.inr (astra4u_Round4Package_nat_1636 A.natDegree E.natDegree F.natDegree G.natDegree h hAG hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1179 A.natDegree F.natDegree G.natDegree h hAG hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1180 A.natDegree F.natDegree G.natDegree h hAG hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2817 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 hcq2 h hAG hcq6)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (astra4u_Round4Package_nat_0850 A.natDegree B.natDegree hApos hBn)
      · exact Or.inr (astra4u_Round4Package_nat_1588 A.natDegree C.natDegree F.natDegree G.natDegree hcq1 hAG h hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1629 A.natDegree D.natDegree F.natDegree G.natDegree hcq4 hcq2 hAG h)
      · exact Or.inr (astra4u_Round4Package_nat_1638 A.natDegree E.natDegree F.natDegree G.natDegree hAG h hcq9 hcq6)
      · exact Or.inr (astra4u_Round4Package_nat_1182 A.natDegree F.natDegree G.natDegree h hAG hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1183 A.natDegree F.natDegree G.natDegree hApos h hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2818 A.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hcq1 hcq2 h hAG hcq9 hcq6)
  have hrest : (piQuarticChamberRest0810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest0810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hAG hcq1 hcq2; omega) (by clear * - hAG hcq1; omega) (by clear * - hcq9; omega) (by clear * - hAG hcq1; omega) (by clear * - hAG hcq1 hcq2 hcq9; omega) (by clear * - hAG hcq1 hcq6; omega) (by clear * - hAG hcq2 hcq6; omega) hbl' hbbeta' (Or.inr (by clear * - hAG hcq1 hcq2 hcq4 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq6 hcq9 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq1 hApos; omega)) (Or.inr (by clear * - hcq1 hcq9 hApos; omega))
  have hlead : (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace0810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  exact (Nat.ne_of_gt hdpos) hpi
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG2810 A B C D E F G)
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
      · exact Or.inr (astra4u_Round4Package_nat_1208 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1399 A.natDegree B.natDegree E.natDegree F.natDegree h hcq7 hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1463 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2819 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hcq1 hcq7 hcq0 h hcq13 hcq5 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1210 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1401 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1465 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2820 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree hcq1 hcq7 h hcq13 hcq5 hcq10)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq13 h)
      · exact Or.inr (astra4u_Round4Package_nat_1212 A.natDegree B.natDegree C.natDegree F.natDegree hcq1 h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_1403 A.natDegree B.natDegree E.natDegree F.natDegree hcq7 h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1466 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_1673 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree h hcq1 hcq13 hcq5 hcq10)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq13; omega) (by clear * - hcq10 hcq13; omega) (by clear * - hcq3; omega) (by clear * - hcq7 hcq10 hcq13; omega) (by clear * - hcq1 hcq5 hcq13; omega) (by clear * - hcq1 hcq13; omega) (by clear * - hcq0 hcq1; omega) (by clear * - hcq5; omega) (by clear * - hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos hcq10 hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq1 hcq7 hApos hcq13; omega)) (Or.inr (by clear * - hcq5 hcq10 hcq13; omega)) (Or.inr (by clear * - hcq1 hcq10 hcq13; omega)) (Or.inr (by clear * - hApos hcq13; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·BG` dies on the `μ` face `A.natDegree + B.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG4810 A B C D E F G)
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
      · exact Or.inr (astra4u_Round4Package_nat_1913 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1341 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2150 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1102 A.natDegree B.natDegree F.natDegree h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1467 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2821 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq5 hcq9 hcq10)
  have hbbeta' : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1105 A.natDegree B.natDegree F.natDegree h hcq13)
      · exact Or.inr (astra4u_Round4Package_nat_1915 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1343 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2152 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1109 A.natDegree B.natDegree F.natDegree h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1469 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2822 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq5 hcq9 hcq10)
  have hbdelta' : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (astra4u_Round4Package_nat_1112 A.natDegree B.natDegree F.natDegree hcq13 h)
      · exact Or.inr (astra4u_Round4Package_nat_1917 A.natDegree B.natDegree C.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2)
      · exact Or.inr (astra4u_Round4Package_nat_1345 A.natDegree B.natDegree D.natDegree F.natDegree h hcq13 hcq5)
      · exact Or.inr (astra4u_Round4Package_nat_2154 A.natDegree B.natDegree E.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq9)
      · exact Or.inr (astra4u_Round4Package_nat_1116 A.natDegree B.natDegree F.natDegree h hcq13 hcq10)
      · exact Or.inr (astra4u_Round4Package_nat_1470 A.natDegree B.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (astra4u_Round4Package_nat_2466 A.natDegree B.natDegree C.natDegree D.natDegree F.natDegree G.natDegree h hcq0 hcq13 hcq2 hcq5 hcq10)
  have hrest : (muQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq2 hcq13; omega) (by clear * - hcq10 hcq13; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq9 hcq13; omega) (by clear * - hcq0 hcq2 hcq5 hcq13; omega) (by clear * - hcq0 hcq2 hcq13; omega) (by clear * - hcq2; omega) (by clear * - hcq5; omega) (by clear * - hcq7; omega) hbl' hbbeta' (Or.inr (by clear * - hcq0 hcq2 hcq5 hcq13; omega)) hbdelta' (Or.inr (by clear * - hcq0 hcq2 hcq7 hcq10 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq3 hcq5 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq13; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq10 hcq13; omega))
  have hlead : (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberFace4810_natDegree A B C D E F G hAne hBne hFne
  rw [degreeZeroMuQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hmu
  exact (Nat.ne_of_gt hdpos) hmu

end QuarticChamberKills810

end Max11DegreeRoutes
