import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIILoadedNinthScratch
import Fable68ScaleTwoAlignedNonsquareMixedThirdRowScratch

/-! # Conjugate-root matching for the refined component III

The loaded-row descent is local at one simple root of the nonsquare quadratic
core.  This file records the complementary root without assuming that it lies
on the same component.  The all-roots lower-third packet gives the exact
component there, while vanishing at both roots globalizes to divisibility by
the quadratic core.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

section RefinedIIIConjugateAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- A specified simple root of a split quadratic has a distinct complementary
root.  This is the existence companion to `natDegree_two_roots_exhaust_68`. -/
theorem simpleQuadratic_exists_other_root_68
    (H : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (a : k) (ha : H.eval a = 0) :
    ∃ c : k, c ≠ a ∧ H.eval c = 0 := by
  classical
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hlin : X - C a ∣ H := by
    rw [dvd_iff_isRoot]
    exact ha
  obtain ⟨Q, hQ⟩ := hlin
  have hlinne : (X - C a : k[X]) ≠ 0 := X_sub_C_ne_zero a
  have hQne : Q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hQ
    exact hH hQ
  have hQdeg : Q.natDegree = 1 := by
    have hmul := natDegree_mul hlinne hQne
    rw [← hQ, hdeg, natDegree_X_sub_C] at hmul
    omega
  have hdegreeQ : Q.degree ≠ 0 := by
    rw [degree_eq_natDegree hQne, hQdeg]
    decide
  obtain ⟨c, hcQ⟩ := IsAlgClosed.exists_root Q hdegreeQ
  have hcQ0 : Q.eval c = 0 := IsRoot.eq_zero hcQ
  have hcH : H.eval c = 0 := by
    rw [hQ]
    simp [eval_mul, hcQ0]
  refine ⟨c, ?_, hcH⟩
  intro hca
  subst c
  have hderiv : H.derivative.eval a = 0 := by
    rw [hQ, derivative_mul]
    simp [eval_add, eval_mul, hcQ0]
  exact hsimple a ha hderiv

/-- Exact finite allocation at the root conjugate to a deep refined-III root.
The first conjunct retains the complete lower-third source packet.  The
remaining disjunction says that the conjugate root is common, component II,
or component III; in the latter two cases every matching zero is globalized
to an honest core divisibility. -/
def terminalRefinedIIIConjugateMatching68
    (H A b D w phi e K : k[X]) (j c : k) : Prop :=
  terminalPhiDivisorLowerThirdClassification68 (A.eval c)
      (H.derivative.eval c) (6 * j * (H.derivative.eval c) ^ 3)
      b D w phi e K c ∧
    (((A.eval c * b.eval c - 3 * D.eval c = 0) ∧
        (phi.eval c + 2 * A.eval c * w.eval c = 0)) ∨
      (b.eval c = 0 ∧ D.eval c = 0 ∧ H ∣ D) ∨
      (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
        ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K))))

theorem terminalRefinedIII_conjugate_matching_68
    (H A b D w phi e K : k[X]) (j a : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hclass : ∀ x : k, H.eval x = 0 →
      terminalPhiDivisorLowerThirdClassification68 (A.eval x)
        (H.derivative.eval x) (6 * j * (H.derivative.eval x) ^ 3)
        b D w phi e K x) :
    ∃ c : k, c ≠ a ∧ H.eval c = 0 ∧
      terminalRefinedIIIConjugateMatching68 H A b D w phi e K j c := by
  obtain ⟨c, hca, hc⟩ :=
    simpleQuadratic_exists_other_root_68 H hdeg hsimple a ha
  have hcc := hclass c hc
  have hdvdW : w.eval c = 0 → H ∣ w := fun hwc =>
    dvd_of_two_simple_root_evals_68 H w hdeg hsimple a c hca.symm ha hc hwa hwc
  have hdvdPhi : phi.eval c = 0 → H ∣ phi := fun hpc =>
    dvd_of_two_simple_root_evals_68 H phi hdeg hsimple a c hca.symm ha hc hphia hpc
  have hdvdD : D.eval c = 0 → H ∣ D := fun hDc =>
    dvd_of_two_simple_root_evals_68 H D hdeg hsimple a c hca.symm ha hc hDa hDc
  have hdvdK : K.eval c = 0 → H ∣ K := fun hKc =>
    dvd_of_two_simple_root_evals_68 H K hdeg hsimple a c hca.symm ha hc hKa hKc
  refine ⟨c, hca, hc, hcc, ?_⟩
  rcases hcc.1 with hcommon | hrest
  · exact Or.inl ⟨hcommon.1, hcommon.2.1⟩
  rcases hrest with hII | hIII
  · exact Or.inr (Or.inl ⟨hII.2.1, hII.2.2.1, hdvdD hII.2.2.1⟩)
  · right; right
    refine ⟨hIII.2.1, hIII.2.2.1, hdvdW hIII.2.1,
      hdvdPhi hIII.2.2.1, ?_⟩
    rcases hIII.2.2.2 with hDbranch | hKbranch
    · exact Or.inl ⟨hDbranch.1, hdvdD hDbranch.1⟩
    · exact Or.inr ⟨hKbranch.1, hdvdK hKbranch.1⟩

end RefinedIIIConjugateAlgebra68

end Max11DegreeRoutes
