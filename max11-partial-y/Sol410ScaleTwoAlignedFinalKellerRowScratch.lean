import Fable410ScaleTwoAlignedEleventhFaceScratch

/-! # Final literal Keller row on the aligned `(4,10)` scale-two source

The verified aligned tower consumes the degree-`11` through degree-`1`
Jacobian coefficients.  This file records the only remaining coefficient on
the *same normalized source*: the degree-`0` Keller row

`p₀' q₁ - p₁ q₀' = C j`, with the original nonzero Keller constant `j`.

This is a source-honest final-row handoff, not a closure claim.  No transverse
degree bound, finite-root argument, or new witness is introduced.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-- The last coefficient of the `(4,10)` Keller identity. -/
theorem alignedFinalCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
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

/-- Source-facing final-row packet on the exact normalized aligned source.
The imported predecessor supplies all higher aligned rows and their chamber
inventory; this theorem adds the original nonzero constant row. -/
theorem normalized410ScaleTwo_alignedFinalKellerRow
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ j : K, j ≠ 0 ∧
      (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp4, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  refine ⟨j, hj, ?_⟩
  exact alignedFinalCoefficientJacobianRow_410 hp hq hjac

#print axioms alignedFinalCoefficientJacobianRow_410
#print axioms normalized410ScaleTwo_alignedFinalKellerRow

end Max11DegreeRoutes
