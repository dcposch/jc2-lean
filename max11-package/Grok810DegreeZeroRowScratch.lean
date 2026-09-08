import LowScale46NormalForm

/-! # Degree-zero Jacobian row of a monic octic-decic pair

Lane Z0 of the `(8,10)` chamber map.  The Jacobian of an octic-decic pair
has `Y`-degree at most `17`; coefficients `16` through `1` are first-integral
rows, and coefficient `0` is the inhomogeneous final row.  After the Pi
chain consumes degree `1`, this is the unique unused Keller coefficient.

This file records that last row in the two forms the later primitive lane
consumes:

* the exact coefficient-`0` identity of a depressed monic octic-decic
  differential Jacobian, the `(8,10)` analogue of
  `differentialJacobian_coeff_0` / `differentialJacobian_coeff_0_monicQuarticDecic`;
* the source-facing bivariate identity
  `p₀' q₁ - p₁ q₀' = C j` on a literal `Normalized810LeadingCoreSource`,
  the `(8,10)` analogue of `alignedFinalCoefficientJacobianRow_410`.

The row equals the original nonzero Keller constant, so it is not a first
integral and it clears no defect.  No pole order, clearing power, or
`h^{97}` jet is introduced.  Affine depression to `C(j)/h₀` is left to the
later source-wrapper lane; whether that depression is a simple pole is
not claimed here.

No total-degree or twice-prime theorem is used.  This is not a chamber
closure.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-! ## Literal source-facing final Keller coefficient -/

/-- The degree-`0` Jacobian coefficient for outer degrees `(8,10)` is the
last row of the tower and is inhomogeneous: `p₀' q₁ - p₁ q₀' = j`, the
Keller constant itself.  There is no unused row below it. -/
theorem degreeZeroCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 0) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) =
      ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  linear_combination hcoeff

/-- Source-facing degree-`0` row on any normalized `(8,10)` core, including
both residual scales.  The aligned hypothesis is not used: the last
coefficient is the original Keller constant on every face. -/
theorem normalized810_degreeZeroJacobianRow
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]} {n : ℕ}
    (hsource : Normalized810LeadingCoreSource P Q H n) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ j : K, j ≠ 0 ∧
      (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp8, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  refine ⟨j, hj, ?_⟩
  exact degreeZeroCoefficientJacobianRow_810 hp hq hjac

/-! ## Depressed monic octic-decic coefficient `0` -/

section DegreeZeroDepressedRow810

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Degree zero of the differential Jacobian of a depressed monic octic and
a monic decic.  The high-degree assumptions are retained for a uniform API
with the already verified rows fifteen through one.  The identity itself
uses only the constant/linear coefficient pairs: `W G' - F X'`. -/
theorem differentialJacobian_coeff_0_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (_hf_high : ∀ n, 8 < n → f.coeff n = 0) (_hf8 : f.coeff 8 = 1)
    (_hf7 : f.coeff 7 = 0)
    (_hg_high : ∀ n, 10 < n → g.coeff n = 0) (_hg10 : g.coeff 10 = 1)
    (_hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 0 =
      g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) = ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 0 =
        g.coeff 1 * d (f.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti, Finset.sum_singleton,
      coeff_coefficientDeriv, Polynomial.coeff_derivative]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 0 =
        f.coeff 1 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti, Finset.sum_singleton,
      coeff_coefficientDeriv, Polynomial.coeff_derivative]
    ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

/-- A constant depressed monic differential Jacobian makes the degree-zero
row equal that same constant.  The later primitive lane consumes this
identity as `dρ = (degree-0 row)`. -/
theorem degreeZeroRow_eq_constant_of_monic_differentialJacobian
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c) :
    g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) = c := by
  have hrow := differentialJacobian_coeff_0_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL
  have hconstant : (differentialJacobian d f g).coeff 0 = c := by
    have h := congrArg (fun t : F[X] => t.coeff 0) hjac
    simpa using h
  exact hrow.symm.trans hconstant

end DegreeZeroDepressedRow810

#print axioms degreeZeroCoefficientJacobianRow_810
#print axioms normalized810_degreeZeroJacobianRow
#print axioms differentialJacobian_coeff_0_monicOcticDecic
#print axioms degreeZeroRow_eq_constant_of_monic_differentialJacobian

end Max11DegreeRoutes
