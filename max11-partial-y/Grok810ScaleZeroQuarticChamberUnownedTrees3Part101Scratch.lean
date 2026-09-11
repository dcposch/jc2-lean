import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedTreeRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeCertsScratch
import Grok810ScaleZeroQuarticChamberN7BandsScratch
import Grok810ScaleZeroQuarticChamberUnownedTreeRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreePiecesScratch

/-! # Unowned plan trees, `(8,10)` scale zero

9 chambers that need a nested case split whose leaves include a
load kill (a load column alone on top forces `p = 0`) or a tied-load
top-coefficient system.  Every pivot orientation, every face and every
load-column verdict is re-derived here with the exact Farkas engine;
the cofactors are the plan's, rescaled to these rows and re-checked.
10 scalar certificates.  Untracked working note.
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

section QuarticChamberUnownedTrees3810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DEFG` / `DD·DE·EE` dies on a plan tree (load kills and tied-load systems included). -/
theorem quarticChamberDEFG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG4810 A B C D E F G)
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
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  rcases lt_trichotomy (D.natDegree + 2 * E.natDegree) (3 * A.natDegree) with hpv0 | hpv0 | hpv0
  ·
    rcases lt_trichotomy (A.natDegree + D.natDegree + F.natDegree) (E.natDegree + G.natDegree) with hpv1 | hpv1 | hpv1
    ·
      have hdpos : 0 < E.natDegree + G.natDegree := by
        clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1; omega
      have hdzpos : 0 < E.natDegree + G.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos; omega
      obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
        quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
        have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq2 hq5; omega)
      have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
        have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
      have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
        have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
          rcases hbdelta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
        rcases hbdeltas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq2; omega)
      have hrest : (xiQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < E.natDegree + G.natDegree :=
        xiQuarticChamberRest9502810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by omega) (by omega) hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hq0 hApos; omega))
      have hlead : (xiQuarticChamberFace9502810 A B C D E F G).natDegree =
          E.natDegree + G.natDegree :=
        xiQuarticChamberFace9502810_natDegree A B C D E F G hEne hGne
      rw [degreeZeroXiQuartic810_eq_face9502_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hxiDeg
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos hxiDeg; omega
    ·
      rcases lt_trichotomy (2 * D.natDegree) (F.natDegree) with hpv2 | hpv2 | hpv2
      ·
        have hdp1 : A.natDegree < A.natDegree + D.natDegree + G.natDegree := by
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        have hdz1 : 0 < A.natDegree + D.natDegree + G.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
          quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hkap
        obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
          quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA homi hnu hkap
        have hz1l : l = 0 ∨ (7 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz1beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz1delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ 2 * D.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbdelta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz1zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz1theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + D.natDegree + G.natDegree ∧ E.natDegree < A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hr1 : (n3QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < A.natDegree + D.natDegree + G.natDegree :=
          n3QuarticChamberRest9502810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdz1 hBz hCz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) hz1l hz1beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz1delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz1zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz1theta
        have hsy0 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).coeff (A.natDegree + D.natDegree + G.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
            A B C D E F G hApos homi hnu
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hle; omega
        rw [degreeZeroN3Quartic810_eq_face9502_add_rest, coeff_add,
          coeff_eq_zero_of_natDegree_lt hr1, add_zero,
          n3QuarticChamberFace9502810_coeff_top hAne hDne hEne hFne hGne (B := B) (C := C) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)] at hsy0
        have hdp3 : A.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree := by
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        have hdz3 : 0 < 2 * A.natDegree + D.natDegree + G.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
          quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hkap
        obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
          quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA homi hnu hkap
        have hz3l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 5 * A.natDegree + E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * D.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * F.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * D.natDegree + E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz3beta : beta = 0 ∨ (7 * A.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * F.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz3delta : delta = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbdelta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz3zeta : zeta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ 2 * D.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz3theta : theta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree ∧ G.natDegree < 2 * A.natDegree + D.natDegree + G.natDegree) := by
          rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hr3 : (n4QuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < 2 * A.natDegree + D.natDegree + G.natDegree :=
          n4QuarticChamberRest9503810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdz3 hBz hCz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) hz3l hz3beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz3delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz3zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz3theta
        have hsy2 : (degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).coeff (2 * A.natDegree + D.natDegree + G.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          have hle := degreeZeroN4Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
            A B C D E F G hApos hprim homi
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hle; omega
        rw [degreeZeroN4Quartic810_eq_face9503_add_rest, coeff_add,
          coeff_eq_zero_of_natDegree_lt hr3, add_zero,
          n4QuarticChamberFace9503810_coeff_top hAne hDne hEne hFne hGne (B := B) (C := C) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)] at hsy2
        have hdp5 : 0 < A.natDegree + 2 * F.natDegree := by
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        have hdz5 : 0 < A.natDegree + 2 * F.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
          quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hkap
        have hz5l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz5beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz5delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
          rcases hbdelta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hr5 : (piQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
          piQuarticChamberRest9502810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdz5 hBz hCz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) hz5l hz5beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz5delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega))
        have hsy4 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).coeff (A.natDegree + 2 * F.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hpiDeg]
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        rw [degreeZeroPiQuartic810_eq_face9502_add_rest, coeff_add,
          coeff_eq_zero_of_natDegree_lt hr5, add_zero,
          piQuarticChamberFace9502810_coeff_top hAne hFne hGne (B := B) (C := C) (D := D) (E := E) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)] at hsy4
        have hdp7 : 0 < A.natDegree + D.natDegree + F.natDegree := by
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        have hdz7 : 0 < A.natDegree + D.natDegree + F.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
          quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA hkap
        have hz7l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz7beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hz7delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbdelta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 h; omega)
        have hr7 : (xiQuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
          xiQuarticChamberRest9503810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdz7 hBz hCz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega) hz7l hz7beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) hz7delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega))
        have hsy6 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hxiDeg]
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        rw [degreeZeroXiQuartic810_eq_face9503_add_rest, coeff_add,
          coeff_eq_zero_of_natDegree_lt hr7, add_zero,
          xiQuarticChamberFace9503810_coeff_top hAne hDne hEne hFne hGne (B := B) (C := C) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega)] at hsy6
        exact quarticUnownedTree6810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff  hsy0 hsy2 hsy4 hsy6 hEc hGc
      ·
        have hdpos : 0 < D.natDegree + E.natDegree := by
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        have hdzpos : 0 < D.natDegree + E.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos; omega
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
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - h hq0 hq2; omega)
            · exact Or.inr (by clear * - h hq0 hq5; omega)
          rcases hbls with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
        have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
          have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbbeta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - h hq0 hq2; omega)
            · exact Or.inr (by clear * - h hq0 hq5; omega)
          rcases hbbetas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
        have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
          have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbdelta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - h hq0 hq2; omega)
            · exact Or.inr (by clear * - h hq0 hq5; omega)
          rcases hbdeltas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq0 hApos; omega)
        have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
          · exact Or.inr (by clear * - h hq0 hq2; omega)
          · exact Or.inr (by clear * - h hq0 hq5; omega)
        have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
          rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq0 hq5; omega)
          · exact Or.inr (by clear * - h hq2; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hCn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hCn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hq0 hApos; omega)
        have hrest : (kappaQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < D.natDegree + E.natDegree :=
          kappaQuarticChamberRest9501810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hq0 hApos hdzpos; omega)) hzzeta hztheta
        have hlead : (kappaQuarticChamberFace9501810 A B C D E F G).natDegree =
            D.natDegree + E.natDegree :=
          kappaQuarticChamberFace9501810_natDegree A B C D E F G hDne hEne
        rw [degreeZeroKappaQuartic810_eq_face9501_add_rest,
          natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
          at hkap
        clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos hkap; omega
      ·
        have hdpos : 0 < D.natDegree + E.natDegree := by
          clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2; omega
        have hdzpos : 0 < D.natDegree + E.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos; omega
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
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - h hq0 hq2; omega)
            · exact Or.inr (by clear * - h hq0 hq5; omega)
          rcases hbls with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
        have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
          have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbbeta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - h hq0 hq2; omega)
            · exact Or.inr (by clear * - h hq0 hq5; omega)
          rcases hbbetas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
        have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
          have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
            rcases hbdelta with h | h | h | h | h | h | h
            · exact Or.inl h
            · exact absurd h (by clear * - hBn hApos; omega)
            · exact absurd h (by clear * - hCn hApos; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
            · exact Or.inr (by clear * - h hq0 hq2; omega)
            · exact Or.inr (by clear * - h hq0 hq5; omega)
          rcases hbdeltas with h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq0 hApos; omega)
        have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos h; omega)
          · exact Or.inr (by clear * - h hq0 hq2; omega)
          · exact Or.inr (by clear * - h hq0 hq5; omega)
        have hztheta : theta = 0 ∨ (A.natDegree < D.natDegree + E.natDegree) := by
          rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (by clear * - h hq0 hq5; omega)
          · exact Or.inr (by clear * - h hq2; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hCn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hCn hq0 hApos; omega)
          · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hBn hCn hq0 hq2 hApos; omega)
          · exact Or.inr (by clear * - h hq0 hApos; omega)
        have hrest : (kappaQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree < D.natDegree + E.natDegree :=
          kappaQuarticChamberRest9501810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
            A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hq0 hApos hdzpos; omega)) hzzeta hztheta
        have hlead : (kappaQuarticChamberFace9501810 A B C D E F G).natDegree =
            D.natDegree + E.natDegree :=
          kappaQuarticChamberFace9501810_natDegree A B C D E F G hDne hEne
        rw [degreeZeroKappaQuartic810_eq_face9501_add_rest,
          natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
          at hkap
        clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hpv2 hdpos hkap; omega
    ·
      have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
        clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1; omega
      have hdzpos : 0 < A.natDegree + D.natDegree + F.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos; omega
      obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
        quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G hA hkap
      have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbl with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
        rcases hbls with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq2 hq5; omega)
      have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbbeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
        rcases hbbetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
      have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbdelta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd h (by clear * - hBn hApos; omega)
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - h hAD hq2; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
        rcases hbdeltas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq2; omega)
      have hzzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
        have hbzetas : zeta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
          rcases hbzeta with h | h | h | h | h | h | h
          · exact Or.inl h
          · exact absurd hBz h
          · exact absurd h (by clear * - hCn hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
          · exact Or.inr (by clear * - h hApos; omega)
          · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos h; omega)
        rcases hbzetas with h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq2; omega)
      have hrest : (xiQuarticChamberRest9504810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
        xiQuarticChamberRest9504810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
          A B C D E F G hdzpos hBz hCz (by omega) (by clear * - hq2; omega) hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hApos; omega))
      have hlead : (xiQuarticChamberFace9504810 A B C D E F G).natDegree =
          A.natDegree + D.natDegree + F.natDegree :=
        xiQuarticChamberFace9504810_natDegree A B C D E F G hAne hDne hFne
      rw [degreeZeroXiQuartic810_eq_face9504_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hxiDeg
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hpv1 hdpos hxiDeg; omega
  ·
    have hdpos : 0 < D.natDegree + E.natDegree := by
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hdzpos : 0 < D.natDegree + E.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos; omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
      have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hbl with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hApos; omega)
        · exact absurd h (by clear * - hCn hApos; omega)
        · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
        · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
        · exact Or.inr (by clear * - h hq0 hq2; omega)
        · exact Or.inr (by clear * - h hq0 hq5; omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
    have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
      have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hbbeta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hApos; omega)
        · exact absurd h (by clear * - hCn hApos; omega)
        · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
        · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
        · exact Or.inr (by clear * - h hq0 hq2; omega)
        · exact Or.inr (by clear * - h hq0 hq5; omega)
      rcases hbbetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
    have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
      have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hbdelta with h | h | h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (by clear * - hBn hApos; omega)
        · exact absurd h (by clear * - hCn hApos; omega)
        · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
        · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
        · exact Or.inr (by clear * - h hq0 hq2; omega)
        · exact Or.inr (by clear * - h hq0 hq5; omega)
      rcases hbdeltas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hApos; omega)
    have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hbzeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd hBz h
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos h; omega)
      · exact Or.inr (by clear * - h hq0 hq2; omega)
      · exact Or.inr (by clear * - h hq0 hq5; omega)
    have hrest : (kappaQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < D.natDegree + E.natDegree :=
      kappaQuarticChamberRest9501810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hq0 hApos hdzpos; omega)) hzzeta (Or.inr (by omega))
    have hlead : (kappaQuarticChamberFace9501810 A B C D E F G).natDegree =
        D.natDegree + E.natDegree :=
      kappaQuarticChamberFace9501810_natDegree A B C D E F G hDne hEne
    rw [degreeZeroKappaQuartic810_eq_face9501_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hkap
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos hkap; omega
  ·
    have hdpos : 0 < D.natDegree + E.natDegree := by
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hdzpos : 0 < D.natDegree + E.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos; omega
    obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
      quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hnu hkap
    have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
      have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbl with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq0 hq5; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq5 hApos; omega)
      rcases hbls with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
    have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
      have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbbeta with h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq0 hq5; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAC hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq5 hApos; omega)
      rcases hbbetas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hq0 hq5; omega)
    have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
      have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
        rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by clear * - h hq0 hq5; omega)
        · exact Or.inr (by clear * - h hq2; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hq0 hq2 hApos; omega)
        · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
        · exact Or.inr (by clear * - h hAC hBn hq0 hq5 hApos; omega)
        · exact Or.inr (by clear * - h hAB hAD hBn hq0; omega)
        · exact Or.inr (by clear * - h hAC hAD hCn hq0; omega)
        · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
      rcases hbdeltas with h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hApos; omega)
    have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hq0 hq5; omega)
      · exact Or.inr (by clear * - h hq2; omega)
      · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hq0 hq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hq0 hq5 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hq0 hq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hq0 hq2; omega)
      · exact Or.inr (by clear * - h hAC hBn hq0 hq5 hApos; omega)
    have hrest : (kappaQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < D.natDegree + E.natDegree :=
      kappaQuarticChamberRest9501810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by clear * - hq0 hApos hdzpos; omega)) hzzeta (Or.inr (by omega))
    have hlead : (kappaQuarticChamberFace9501810 A B C D E F G).natDegree =
        D.natDegree + E.natDegree :=
      kappaQuarticChamberFace9501810_natDegree A B C D E F G hDne hEne
    rw [degreeZeroKappaQuartic810_eq_face9501_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hkap
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos hkap; omega

end QuarticChamberUnownedTrees3810

end Max11DegreeRoutes
/-! # Unowned plan trees, `(8,10)` scale zero

9 chambers that need a nested case split whose leaves include a
load kill (a load column alone on top forces `p = 0`) or a tied-load
top-coefficient system.  Every pivot orientation, every face and every
load-column verdict is re-derived here with the exact Farkas engine;
the cofactors are the plan's, rescaled to these rows and re-checked.
10 scalar certificates.  Untracked working note.
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

section QuarticChamberUnownedTrees3810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DEFG` / `EE` dies on a plan tree (load kills and tied-load systems included). -/
theorem quarticChamberDEFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG8810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  rcases lt_trichotomy (G.natDegree) (2 * E.natDegree) with hpv0 | hpv0 | hpv0
  ·
    have hdpos : 0 < 2 * E.natDegree := by
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hdzpos : 0 < 2 * E.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos; omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq2; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4 hq5; omega)
    have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq2; omega)
      · exact Or.inr (by clear * - h hq0 hq4 hApos; omega)
      · exact Or.inr (by clear * - h hAE hq2 hq4; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4 hq5; omega)
    have hrest : (muQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < 2 * E.natDegree :=
      muQuarticChamberRest9502810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz (by clear * - hq0; omega) (by clear * - hq2; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by clear * - hq0 hq2; omega)) (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hq0 hApos; omega))
    have hlead : (muQuarticChamberFace9502810 A B C D E F G).natDegree =
        2 * E.natDegree :=
      muQuarticChamberFace9502810_natDegree A B C D E F G hEne
    rw [degreeZeroMuQuartic810_eq_face9502_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hmuDeg
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos hmuDeg; omega
  ·
    have hdp1 : 0 < 2 * E.natDegree := by
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hdz1 : 0 < 2 * E.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hz1l : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hz1beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hlf1 : (muQuarticChamberRestLF9502810 A B C D E F G).natDegree < 2 * E.natDegree :=
      muQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
        A B C D E F G hdz1 hBz hCz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)
    have hr1 : (muQuarticChamberRestOff2810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < 2 * E.natDegree :=
      muQuarticChamberRestOff2810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdz1 hBz hCz hlf1 hz1l hz1beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega))
    have hsy0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmuDeg]
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hcc1 : (muQuarticColumnTop2810 gamma A B C D E F G).coeff
        (2 * E.natDegree) =
        (3 / 4 : k) * gamma * (G.leadingCoeff) := by
      rw [show (2 * E.natDegree) = (G.natDegree) from by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega]
      exact muQuarticColumnTop2810_coeff gamma hGne
    rw [degreeZeroMuQuartic810_eq_face9502_add_rest,
      muQuarticChamberRest9502810_split2 l beta gamma delta epsilon zeta eta theta A B C D E F G,
      coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt hr1, add_zero,
      hcc1,
      muQuarticChamberFace9502810_coeff_top hEne (A := A) (B := B) (C := C) (D := D) (F := F) (G := G)] at hsy0
    have hdp3 : 2 * A.natDegree < A.natDegree + F.natDegree + G.natDegree := by
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hdz3 : 0 < A.natDegree + F.natDegree + G.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
      quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hprim homi hnu hkap
    have hz3l : l = 0 ∨ (8 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 5 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + D.natDegree + F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + E.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * D.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * G.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hz3beta : beta = 0 ∨ (7 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hz3delta : delta = 0 ∨ (6 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hz3zeta : zeta = 0 ∨ (5 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * D.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases hbzeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd hBz h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hz3theta : theta = 0 ∨ (4 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hr3 : (n6QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < A.natDegree + F.natDegree + G.natDegree :=
      n6QuarticChamberRest9500810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdz3 hBz hCz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega) hz3l hz3beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)) hz3delta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)) hz3zeta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)) hz3theta
    have hsy2 : (degreeZeroN6Quartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + F.natDegree + G.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle := degreeZeroN6Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
        A B C D E F G hApos hprim homi hnu
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hle; omega
    rw [degreeZeroN6Quartic810_eq_face9500_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hr3, add_zero,
      n6QuarticChamberFace9500810_coeff_top hAne hFne hGne (B := B) (C := C) (D := D) (E := E)] at hsy2
    exact quarticUnownedTree7810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff gamma hsy0 hsy2 hAc hFc hGc
  ·
    have hdp4 : 0 < G.natDegree := by
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hdz4 : 0 < G.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hz4l : l = 0 ∨ (3 * A.natDegree + D.natDegree < G.natDegree ∧ 2 * A.natDegree + F.natDegree < G.natDegree ∧ D.natDegree + E.natDegree < G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hz4beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < G.natDegree ∧ A.natDegree + F.natDegree < G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
      · exact Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 h; omega)
    have hlf4 : (muQuarticChamberRestLF9502810 A B C D E F G).natDegree < G.natDegree :=
      muQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
        A B C D E F G hdz4 hBz hCz (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega) (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)
    have hr4 : (muQuarticChamberRestOff2810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < G.natDegree :=
      muQuarticChamberRestOff2810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdz4 hBz hCz hlf4 hz4l hz4beta (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega)) (Or.inr (by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega))
    have hlk : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (G.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmuDeg]
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hfl4 : (muQuarticChamberFace9502810 A B C D E F G).natDegree
        < G.natDegree := by
      rw [muQuarticChamberFace9502810_natDegree A B C D E F G hEne]
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    rw [degreeZeroMuQuartic810_eq_face9502_add_rest,
      muQuarticChamberRest9502810_split2 l beta gamma delta epsilon zeta eta theta A B C D E F G,
      coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt hfl4, zero_add,
      coeff_eq_zero_of_natDegree_lt hr4, add_zero,
      muQuarticColumnTop2810_coeff gamma hGne] at hlk
    have hzerogamma : gamma = 0 := by
      rcases mul_eq_zero.mp hlk with h | h
      · rcases mul_eq_zero.mp h with h2 | h2
        · exact absurd h2 (by norm_num)
        · exact h2
      · exact absurd h hGc
    have hdpos : 0 < 2 * E.natDegree := by
      clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0; omega
    have hdzpos : 0 < 2 * E.natDegree := by clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos; omega
    obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
      quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G hA hkap
    have hzl : l = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * E.natDegree ∧ D.natDegree + E.natDegree < 2 * E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq2; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4 hq5; omega)
    have hzbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * E.natDegree ∧ A.natDegree + F.natDegree < 2 * E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact absurd h (by clear * - hCn hApos; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq2; omega)
      · exact Or.inr (by clear * - h hq0 hq4 hApos; omega)
      · exact Or.inr (by clear * - h hAE hq2 hq4; omega)
      · exact Or.inr (by clear * - h hAE hq0 hq4 hq5; omega)
    have hrest : (muQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree < 2 * E.natDegree :=
      muQuarticChamberRest9502810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
        A B C D E F G hdzpos hBz hCz (by clear * - hq0; omega) (by clear * - hq2; omega) hzl hzbeta (Or.inl hzerogamma) (Or.inr (by clear * - hq0 hq2; omega)) (Or.inr (by clear * - hq0 hApos; omega)) (Or.inr (by clear * - hq0 hApos; omega))
    have hlead : (muQuarticChamberFace9502810 A B C D E F G).natDegree =
        2 * E.natDegree :=
      muQuarticChamberFace9502810_natDegree A B C D E F G hEne
    rw [degreeZeroMuQuartic810_eq_face9502_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
      at hmuDeg
    clear * - hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hpv0 hdpos hmuDeg; omega

end QuarticChamberUnownedTrees3810

end Max11DegreeRoutes
