import Grok610DegreeZeroMixedArmClosureScratch

/-! # Multiple-root chamber of the `(6,10)` degree-zero face

Untracked working note.  No tracked file was edited.

The linear-root chamber of the degree-zero face is already closed:
`degreeZeroFace610_linearRoot` is False, by the bounded tower (jet
quotient `h`-degree at most six, pole obstructions per order, then
cancel-six exposing `rho` as a polynomial, contradicting
`rho' = C j / h0` with `j ≠ 0`).

This file asks what root multiplicities of the local scale `h0` remain.

## Constraining theorem

Backwire, LocalPole, the source wrapper, and every subsequent peel
require `h0.natDegree = 1` as a hypothesis.  That is not an extra
assumption at scale two: `normalized610ScaleTwo_nonzeroFace_has_linear_root`
(via `squareCore_of_nonzero_imprimitiveRelation_610` and
`Polynomial.natDegree_pow`) already forces

`H.natDegree = 2` and `H = h0 ^ 2`  ⇒  `h0.natDegree = 1`.

A degree-one polynomial is separable: its derivative is a nonzero
constant, so `IsCoprime h0 (derivative h0)` and every root has
multiplicity exactly one.  The committed Primitive equation
`degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole` does *not* assume
linearity — the right-hand side is `C j / h` for an arbitrary nonzero
local scale — but at scale two that `h` cannot have a multiple root, so
the higher-order pole analogue is never instantiated.

**CLOSED:** the multiple-root chamber of the scale-two degree-zero
nonzero face is empty.

## Mapped residuals

* Scale two, no finite root of `h0`: empty, because a degree-one
  polynomial over a field has a unique simple root.
* Scale zero (`H.natDegree = 0`): `h0` is a nonzero constant and has no
  finite root.  That is the existing scale-zero lane
  (`Fable610ScaleZeroTwelfthDefectScratch`); it is not a residual of
  this chamber and is not closed here.
* Other scales (`H.natDegree ∉ {0, 2}`): not in
  `PlaneKellerNormalized610LowScaleRoute`.
* Aligned face `N = 0`: a different first-face, not opened.

Composing the empty multiple-root/no-root chambers with the committed
linear-root False empties the whole scale-two nonzero first-face.  The
aligned face is not claimed.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section DegreeZeroMultipleRoot610

variable {k : Type*} [Field k]

/-- Scale two of a square core forces the local scale to be linear.
This is the degree half of `normalized610ScaleTwo_nonzeroFace_has_linear_root`. -/
theorem degreeZeroFace610_h0_natDegree_eq_one_of_scaleTwo
    (H h0 : k[X]) (hh0 : h0 ≠ 0) (hHdegree : H.natDegree = 2)
    (hH : H = h0 ^ 2) :
    h0.natDegree = 1 := by
  have hdegree := congrArg natDegree hH
  rw [hHdegree, natDegree_pow] at hdegree
  omega

/-- A degree-one polynomial has derivative a nonzero constant. -/
theorem linearPolynomial_derivative_eq_C_ne_zero610
    (h0 : k[X]) (hdegree : h0.natDegree = 1) :
    ∃ c : k, c ≠ 0 ∧ derivative h0 = C c := by
  obtain ⟨c, hc, d, hlinear⟩ := natDegree_eq_one.mp hdegree
  refine ⟨c, hc, ?_⟩
  rw [← hlinear]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
    mul_one, add_zero, zero_mul, zero_add]

/-- Linear scales are separable: coprime with their derivative. -/
theorem linearPolynomial_isCoprime_derivative610
    (h0 : k[X]) (hdegree : h0.natDegree = 1) :
    IsCoprime h0 (derivative h0) := by
  obtain ⟨c, hc, hder⟩ :=
    linearPolynomial_derivative_eq_C_ne_zero610 h0 hdegree
  refine ⟨0, C c⁻¹, ?_⟩
  rw [hder, zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ hc, C_1]

/-- Every root of a degree-one polynomial is simple. -/
theorem linearPolynomial_rootMultiplicity_eq_one610
    (h0 : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) :
    h0.rootMultiplicity a = 1 := by
  have hh0 : h0 ≠ 0 := by
    intro hzero
    simp [hzero] at hdegree
  have hpos : 0 < h0.rootMultiplicity a :=
    (rootMultiplicity_pos hh0).mpr hroot
  have hnot : ¬ 1 < h0.rootMultiplicity a := by
    intro hlt
    have hboth := (one_lt_rootMultiplicity_iff_isRoot hh0).mp hlt
    obtain ⟨c, hc, hder⟩ :=
      linearPolynomial_derivative_eq_C_ne_zero610 h0 hdegree
    have hceval : (C c : k[X]).eval a = 0 := by
      rw [← hder]
      exact IsRoot.eq_zero hboth.2
    simp only [eval_C] at hceval
    exact hc hceval
  omega

/-- A degree-one polynomial over a field has a unique simple root. -/
theorem linearPolynomial_exists_root610
    (h0 : k[X]) (hdegree : h0.natDegree = 1) :
    ∃ a : k, h0.eval a = 0 := by
  obtain ⟨c, hc, d, hlinear⟩ := natDegree_eq_one.mp hdegree
  refine ⟨-d / c, ?_⟩
  rw [← hlinear]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  field_simp [hc]
  ring

/-- **CLOSED.** Multiple-root chamber of a scale-two square core: a root
of multiplicity at least two would force `h0.natDegree ≥ 2`, contradicting
`H.natDegree = 2` and `H = h0 ^ 2`. -/
theorem degreeZeroFace610_multipleRoot
    (H h0 : k[X]) (a : k) (hh0 : h0 ≠ 0) (hHdegree : H.natDegree = 2)
    (hH : H = h0 ^ 2) (hmult : 1 < h0.rootMultiplicity a) : False := by
  have hdegree :=
    degreeZeroFace610_h0_natDegree_eq_one_of_scaleTwo H h0 hh0 hHdegree hH
  have hpos : 0 < h0.rootMultiplicity a := Nat.zero_lt_of_lt hmult
  have hroot : h0.eval a = 0 :=
    (rootMultiplicity_pos hh0).mp hpos
  have hone :=
    linearPolynomial_rootMultiplicity_eq_one610 h0 a hdegree hroot
  omega

/-- Scale-two no-root configuration: empty, because the forced linear
scale has a root in `k`. -/
theorem degreeZeroFace610_noRoot_of_scaleTwo
    (H h0 : k[X]) (hh0 : h0 ≠ 0) (hHdegree : H.natDegree = 2)
    (hH : H = h0 ^ 2) :
    ∃ a : k, h0.eval a = 0 :=
  linearPolynomial_exists_root610 h0
    (degreeZeroFace610_h0_natDegree_eq_one_of_scaleTwo H h0 hh0
      hHdegree hH)

/-- Scale-zero mapping: a constant common core has constant square root. -/
theorem degreeZeroFace610_scaleZero_h0_natDegree_eq_zero
    (H h0 : k[X]) (hh0 : h0 ≠ 0) (hHdegree : H.natDegree = 0)
    (hH : H = h0 ^ 2) :
    h0.natDegree = 0 := by
  have hdegree := congrArg natDegree hH
  rw [hHdegree, natDegree_pow] at hdegree
  omega

/-- Scale-zero mapping: a nonzero constant scale has no finite root.
This is the existing scale-zero `(6,10)` lane, not a residual of the
degree-zero linear-root chamber. -/
theorem degreeZeroFace610_scaleZero_noRoot
    (H h0 : k[X]) (a : k) (hh0 : h0 ≠ 0) (hHdegree : H.natDegree = 0)
    (hH : H = h0 ^ 2) :
    h0.eval a ≠ 0 := by
  have hdeg :=
    degreeZeroFace610_scaleZero_h0_natDegree_eq_zero H h0 hh0 hHdegree hH
  have heq : h0 = C (h0.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : h0.coeff 0 ≠ 0 := by
    intro hc0
    apply hh0
    rw [heq, hc0, C_0]
  rw [heq, eval_C]
  exact hcoeff

end DegreeZeroMultipleRoot610

section DegreeZeroScaleTwoNonzeroFace610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing sibling of `degreeZeroFace610_linearRoot` on a
multiple root of `h0`.  The extra packet hypotheses are the same
nonzero first-face data; they are not needed once scale two forces
`h0` linear and separable. -/
theorem degreeZeroFace610_multipleRoot_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hHdegree : H.natDegree = 2) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hlambda : lambda ≠ 0) (hj : j ≠ 0)
    (hmult : 1 < h0.rootMultiplicity a) : False :=
  degreeZeroFace610_multipleRoot H h0 a hh0 hHdegree hH hmult

/-- Scale-two nonzero first-face with a supplied linear root: the
committed linear-root chamber is False.  This is the only remaining
root configuration at this scale. -/
theorem degreeZeroFace610_of_scaleTwo
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hHdegree : H.natDegree = 2) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) (hj : j ≠ 0) :
    False :=
  degreeZeroFace610_linearRoot p q H h0 j lambda a hp hq hh0
    (degreeZeroFace610_h0_natDegree_eq_one_of_scaleTwo H h0 hh0
      hHdegree hH)
    hH hp6 hq10 hN hD hroot hlambda hj

/-- Source-facing exclusion of a normalized scale-two `(6,10)` nonzero
face.  Every such source has a linear local scale
(`normalized610ScaleTwo_nonzeroFace_has_linear_root`); the multiple-root
and no-root chambers are empty above; the linear-root chamber is the
committed False `degreeZeroFace610_linearRoot`.  The aligned face
`N = 0` is not opened. -/
theorem normalized610ScaleTwo_nonzeroFace_false
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    False := by
  dsimp only at hnonzero
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized610ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  exact degreeZeroFace610_linearRoot p q H h0 j lambda a hp hq hh0
    hh0degree hH hp6' hq10' hN' hD hroot hlambda hj

end DegreeZeroScaleTwoNonzeroFace610

#print axioms degreeZeroFace610_h0_natDegree_eq_one_of_scaleTwo
#print axioms linearPolynomial_derivative_eq_C_ne_zero610
#print axioms linearPolynomial_isCoprime_derivative610
#print axioms linearPolynomial_rootMultiplicity_eq_one610
#print axioms linearPolynomial_exists_root610
#print axioms degreeZeroFace610_multipleRoot
#print axioms degreeZeroFace610_noRoot_of_scaleTwo
#print axioms degreeZeroFace610_scaleZero_h0_natDegree_eq_zero
#print axioms degreeZeroFace610_scaleZero_noRoot
#print axioms degreeZeroFace610_multipleRoot_of_source
#print axioms degreeZeroFace610_of_scaleTwo
#print axioms normalized610ScaleTwo_nonzeroFace_false

end Max11DegreeRoutes
