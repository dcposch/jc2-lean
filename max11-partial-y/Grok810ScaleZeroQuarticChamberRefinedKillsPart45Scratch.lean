import Grok810ScaleZeroQuarticChamberRefineScratch

/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

set_option maxHeartbeats 64000000 in
/-- Refined leaf 4 of chamber `BCDEFG` / `CG·EE·CCC` dies on the single-monomial `κ` face. -/
theorem quarticRefinedBCDEFG108L4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG108L4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq9 hrf0 hrf1 hApos hcq10 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
  have hr0 : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq1 hcq4 hrf0; omega) (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega) (by clear * - hcq1 hrf0; omega) (by clear * - hrf0; omega) (by clear * - hrf1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hcq10; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq4 hrf0; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hkap; omega

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
