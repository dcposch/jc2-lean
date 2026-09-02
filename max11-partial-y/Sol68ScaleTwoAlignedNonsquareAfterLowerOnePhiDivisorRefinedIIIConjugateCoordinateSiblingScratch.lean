import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateCommonIIAssemblyScratch

/-! # The remaining conjugate coordinate sibling -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateCoordinateSiblingAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact finite inventory of the conjugate coordinate sibling.  If `b`
already vanishes at the deep root, it rejoins that preserved selector.  If
`r` vanishes at both simple roots, it becomes the global coordinate divisor
`H ∣ r`.  The only remaining allocation is the already verified refined-III
transverse packet at the deep root, with both cubic-coordinate evaluations
made explicit. -/
def terminalRefinedIIIConjugateCoordinateResidual68
    (H t r X b d w phi e K : k[X]) (a c load : k) : Prop :=
  b.eval a = 0 ∨ H ∣ r ∨
    (b.eval a ≠ 0 ∧ r.eval a ≠ 0 ∧
      t.eval c = 0 ∧ (cubicANumerator68 t r).eval c = 0 ∧
      (cubicANumerator68 t r).eval a =
        -(1 / 12 : k) * r.eval a ^ 2 ∧
      (cubicANumerator68 t r).eval a ≠ 0 ∧
      w.derivative.eval a = 0 ∧ phi.derivative.eval a = 0 ∧
      phi.derivative.derivative.eval a = 0 ∧
      b.eval a * phi.derivative.derivative.derivative.eval a +
        18 * w.derivative.derivative.eval a * d.derivative.eval a = 0 ∧
      terminalThirdTripleMiddleDoubleZeroAt68 b w e a -
        terminalThirdPairLeftZeroAt68 d K a = load)

/-- Two-root globalization or the exact deep transverse residual. -/
theorem terminalRefinedIII_conjugate_coordinate_sibling_68
    (H t r X b d w phi e K : k[X]) (a c load : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hX : C 3 * t - r ^ 2 = H * X)
    (hrc : r.eval c = 0)
    (hrefined : b.eval a ≠ 0 →
      terminalPhiDivisorRefinedIIIResidual68 r b d w phi e K a load) :
    terminalRefinedIIIConjugateCoordinateResidual68
      H t r X b d w phi e K a c load := by
  have hxc := congrArg (fun P : k[X] => P.eval c) hX
  simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, hc,
    zero_mul] at hxc
  have htc : t.eval c = 0 := by
    rw [hrc, zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero] at hxc
    linear_combination (1 / 3 : k) * hxc
  have hAc : (cubicANumerator68 t r).eval c = 0 := by
    dsimp only [cubicANumerator68]
    simp [eval_sub, eval_mul, eval_pow, eval_C, htc, hrc]
  rcases eq_or_ne (b.eval a) 0 with hba | hba
  · exact Or.inl hba
  have hxa := congrArg (fun P : k[X] => P.eval a) hX
  simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, ha,
    zero_mul] at hxa
  have hAa : (cubicANumerator68 t r).eval a =
      -(1 / 12 : k) * r.eval a ^ 2 := by
    dsimp only [cubicANumerator68]
    simp only [eval_sub, eval_mul, eval_pow, eval_C]
    linear_combination (1 / 3 : k) * hxa
  by_cases hra : r.eval a = 0
  · right; left
    exact dvd_of_two_simple_root_evals_68 H r hdeg hsimple
      a c hac ha hc hra hrc
  · right; right
    have htrans := (hrefined hba).resolve_left hra
    have hAane : (cubicANumerator68 t r).eval a ≠ 0 := by
      rw [hAa]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hra)
    exact ⟨hba, hra, htc, hAc, hAa, hAane, htrans⟩

end RefinedIIIConjugateCoordinateSiblingAlgebra68

section RefinedIIIConjugateCoordinateSiblingSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Mechanical source wrapper using exactly the all-roots refined-III API
which precedes conjugate matching. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateCoordinateSibling
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X b d w phi e K : k[X]) (a c : k)
    (hdeg : H.natDegree = 2)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hX : C 3 * t - r ^ 2 = H * X)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : d.eval a = 0)
    (hroot : terminalPhiDivisorLowerThirdClassification68
        ((cubicANumerator68 t r).eval a) (H.derivative.eval a)
        (6 * j * H.derivative.eval a ^ 3) b d w phi e K a ∧
      (w.eval a = 0 → phi.eval a = 0 → d.eval a = 0 →
        b.eval a ≠ 0 →
        terminalPhiDivisorRefinedIIIResidual68 r b d w phi e K a
          (6 * j * H.derivative.eval a ^ 3)))
    (hrc : r.eval c = 0) :
    terminalRefinedIIIConjugateCoordinateResidual68 H t r X b d w phi e K
      a c (6 * j * H.derivative.eval a ^ 3) := by
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  apply terminalRefinedIII_conjugate_coordinate_sibling_68 H t r X
    b d w phi e K a c (6 * j * H.derivative.eval a ^ 3)
    hdeg hsimple ha hc hac hX hrc
  intro hba
  exact hroot.2 hwa hphia hDa hba

/-- Replacement rule for the coordinate limb in the merged common/II
inventory; the common-transverse and component-III limbs are unchanged. -/
theorem terminalRefinedIII_commonII_coordinate_refinement_68
    (t r X b d w phi e K : k[X]) (j a c : k)
    (hinventory : terminalRefinedIIIConjugateCommonIIResidual68 H
      (cubicANumerator68 t r) b d w phi e K r j a c)
    (hcoordinate : r.eval c = 0 →
      terminalRefinedIIIConjugateCoordinateResidual68 H t r X
        b d w phi e K a c (6 * j * H.derivative.eval a ^ 3)) :
    terminalRefinedIIIConjugateCoordinateResidual68 H t r X b d w phi e K
        a c (6 * j * H.derivative.eval a ^ 3) ∨
      terminalRefinedIIIConjugateCommonTransverseNext68 H
          (cubicANumerator68 t r) b d w phi e K j a c ∨
      (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
        ((d.eval c = 0 ∧ H ∣ d) ∨ (K.eval c = 0 ∧ H ∣ K))) := by
  rcases hinventory with hrc | hcommon | hIII
  · exact Or.inl (hcoordinate hrc)
  · exact Or.inr (Or.inl hcommon)
  · exact Or.inr (Or.inr hIII)

end RefinedIIIConjugateCoordinateSiblingSource68

end Max11DegreeRoutes
