import LowScale68ScaleTwoAlignedNonsquareIntegratedSAssembly

/-! # Degree-six residual for the aligned nonsquare cubic core -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

section DegreeSixRow68

variable {k : Type*} [Field k] [CharZero k]

/-- The degree-six coefficient of the literal `(6,8)` Keller bracket. -/
theorem seventhCoefficientJacobianRow_68 {p q : k[X][Y]} {j : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j)) :
    (p.coeff 6).derivative * q.coeff 1 +
        (p.coeff 5).derivative * (q.coeff 2 * C (2 : k)) +
        (p.coeff 4).derivative * (q.coeff 3 * C (3 : k)) +
        (p.coeff 3).derivative * (q.coeff 4 * C (4 : k)) +
        (p.coeff 2).derivative * (q.coeff 5 * C (5 : k)) +
        (p.coeff 1).derivative * (q.coeff 6 * C (6 : k)) +
        (p.coeff 0).derivative * (q.coeff 7 * C (7 : k)) -
      ((p.coeff 6 * C (6 : k)) * (q.coeff 1).derivative +
        (p.coeff 5 * C (5 : k)) * (q.coeff 2).derivative +
        (p.coeff 4 * C (4 : k)) * (q.coeff 3).derivative +
        (p.coeff 3 * C (3 : k)) * (q.coeff 4).derivative +
        (p.coeff 2 * C (2 : k)) * (q.coeff 5).derivative +
        p.coeff 1 * (q.coeff 6).derivative) = 0 := by
  have hcoeff := congrArg (fun z : k[X][Y] => z.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1),
        (6, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : C (2 : k) = (2 : k[X]) := C_eq_natCast 2
  have hC3 : C (3 : k) = (3 : k[X]) := C_eq_natCast 3
  have hC4 : C (4 : k) = (4 : k[X]) := C_eq_natCast 4
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC7 : C (7 : k) = (7 : k[X]) := C_eq_natCast 7
  rw [hC2, hC3, hC4, hC5, hC6, hC7]
  linear_combination hcoeff

/-- Root specialization of the degree-six row with all lower auxiliaries
kept explicit. -/
theorem seventhCoefficientJacobianRow_eval_root_68
    {p q : k[X][Y]} {j : k} {H r t s u w : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hp5 : p.coeff 5 = H ^ 2 * r) (hp4 : p.coeff 4 = H * t)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * H ^ 3 * r)
    (hq6 : q.coeff 6 = H ^ 2 * s) (hq5 : q.coeff 5 = H * u)
    (hq4 : q.coeff 4 = w)
    (ha : H.eval a = 0) :
    H.derivative.eval a *
        ((3 : k) * t.eval a * (q.coeff 3).eval a -
          (2 : k) * (p.coeff 2).eval a * u.eval a) +
      (4 : k) * (p.coeff 3).derivative.eval a * w.eval a -
      (3 : k) * (p.coeff 3).eval a * w.derivative.eval a = 0 := by
  have hrow := seventhCoefficientJacobianRow_68 hp hq hjac
  have heval := congrArg (fun f : k[X] => f.eval a) hrow
  simp [hp6, hq8, hp5, hp4, hq7, hq6, hq5, hq4,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, eval_add, eval_sub, eval_mul, eval_pow, eval_C,
    eval_zero, ha] at heval
  linear_combination heval

/-- On the cubic core, the degree-six row is the following exact finite
residual.  In particular this row alone does not force `r=0`; it couples the
new `q₃,p₂` auxiliaries to the transverse derivatives. -/
theorem degreeSix_cubicCore_residual_68
    (d r u w p2 q3 p3' w' : k)
    (ht : (3 : k) * (r ^ 2 / 3) = r ^ 2)
    (hv : (27 : k) * (r ^ 3 / 27) = r ^ 3)
    (hrow : d * (3 * (r ^ 2 / 3) * q3 - 2 * p2 * u) +
      4 * p3' * w - 3 * (r ^ 3 / 27) * w' = 0) :
    d * (r ^ 2 * q3 - 2 * p2 * u) + 4 * p3' * w -
      (1 / 9 : k) * r ^ 3 * w' = 0 := by
  linear_combination hrow

end DegreeSixRow68

end Max11DegreeRoutes
