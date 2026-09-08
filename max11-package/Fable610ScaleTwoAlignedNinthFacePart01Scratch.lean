import Fable610ScaleTwoAlignedEighthFaceScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- The ninth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`6` Jacobian coefficient, the first
aligned row that sees `q₁`. -/
theorem alignedNinthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * q.coeff 1 +
        (p.coeff 5).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 4).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 3).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 2).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 1).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 0).derivative * (q.coeff 7 * Polynomial.C (7 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 1).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 2).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 3).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 4).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 5).derivative +
        p.coeff 1 * (q.coeff 6).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1),
        (6, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  rw [hC2, hC3, hC4, hC5, hC6, hC7]
  linear_combination hcoeff

end Max11DegreeRoutes
