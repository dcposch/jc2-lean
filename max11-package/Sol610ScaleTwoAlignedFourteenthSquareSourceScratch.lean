import Sol610ScaleTwoAlignedThirteenthSquareSourceScratch

/-! # Source-facing degree-one successor for aligned `(6,10)` square sources

The same normalized source witness that supplies the weight-30 and weight-65
first integrals also satisfies the next unused, degree-one Keller row.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

/-- The literal degree-one Jacobian row, kept under a square-route-specific
name so this source packet does not import the incompatible legacy face DAG. -/
theorem alignedFourteenthSquareCoefficientJacobianRow_610
    {K : Type*} [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 1).derivative * q.coeff 1 +
        (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
      ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
        p.coeff 1 * (q.coeff 1).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 1) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (1 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 1 :
      Finset (ℕ × ℕ)) =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC2]
  linear_combination hcoeff

/-- Preserve the exact square-chamber source packet and append the literal
degree-one Jacobian coefficient row without selecting any source witness again.
-/
theorem normalized610ScaleTwo_alignedFourteenthSquareSource_610
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ c xi : K,
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
      alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) =
        Polynomial.C c * H ^ 30 ∧
      localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) 0 =
        Polynomial.C xi * h0 ^ 65 ∧
      (p.coeff 1).derivative * q.coeff 1 +
          (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
        ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
          p.coeff 1 * (q.coeff 1).derivative) = 0 := by
  dsimp only at haligned ⊢
  obtain ⟨κ, c, xi, hM, hthirty, hsixtyfive⟩ :=
    normalized610ScaleTwo_alignedThirteenthSquareSource_610 hsource
      haligned hh0 hHsq
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hrow := alignedFourteenthSquareCoefficientJacobianRow_610 hp hq hjac
  exact ⟨κ, c, xi, hM, hthirty, hsixtyfive, hrow⟩

#print axioms normalized610ScaleTwo_alignedFourteenthSquareSource_610
#print axioms alignedFourteenthSquareCoefficientJacobianRow_610

end Max11DegreeRoutes
