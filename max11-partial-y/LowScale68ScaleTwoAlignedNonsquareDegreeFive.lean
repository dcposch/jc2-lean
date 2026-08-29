import LowScale68ScaleTwoAlignedNonsquareDegreeSix

/-! # Degree-five row and its fresh-coordinate obstruction -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section DegreeFiveRow68

variable {k : Type*} [Field k] [CharZero k]

/-- The next literal, degree-five coefficient of the `(6,8)` Keller
bracket. -/
theorem eighthCoefficientJacobianRow_68 {p q : k[X][Y]} {j : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j)) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * C (2 : k)) +
        (p.coeff 3).derivative * (q.coeff 3 * C (3 : k)) +
        (p.coeff 2).derivative * (q.coeff 4 * C (4 : k)) +
        (p.coeff 1).derivative * (q.coeff 5 * C (5 : k)) +
        (p.coeff 0).derivative * (q.coeff 6 * C (6 : k)) -
      ((p.coeff 6 * C (6 : k)) * (q.coeff 0).derivative +
        (p.coeff 5 * C (5 : k)) * (q.coeff 1).derivative +
        (p.coeff 4 * C (4 : k)) * (q.coeff 2).derivative +
        (p.coeff 3 * C (3 : k)) * (q.coeff 3).derivative +
        (p.coeff 2 * C (2 : k)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) = 0 := by
  have hcoeff := congrArg (fun z : k[X][Y] => z.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : C (2 : k) = (2 : k[X]) := C_eq_natCast 2
  have hC3 : C (3 : k) = (3 : k[X]) := C_eq_natCast 3
  have hC4 : C (4 : k) = (4 : k[X]) := C_eq_natCast 4
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  rw [hC2, hC3, hC4, hC5, hC6]
  linear_combination hcoeff

/-- Root specialization of degree five.  The fresh value `q₂(a)` is kept
visible. -/
theorem eighthCoefficientJacobianRow_eval_root_68
    {p q : k[X][Y]} {j : k} {H r t s u w : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hp5 : p.coeff 5 = H ^ 2 * r) (hp4 : p.coeff 4 = H * t)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * H ^ 3 * r)
    (hq6 : q.coeff 6 = H ^ 2 * s) (hq5 : q.coeff 5 = H * u)
    (hq4 : q.coeff 4 = w) (ha : H.eval a = 0) :
    H.derivative.eval a *
        ((2 : k) * t.eval a * (q.coeff 2).eval a -
          (p.coeff 1).eval a * u.eval a) +
      (3 : k) * ((p.coeff 3).derivative.eval a * (q.coeff 3).eval a -
        (p.coeff 3).eval a * (q.coeff 3).derivative.eval a) +
      (4 : k) * (p.coeff 2).derivative.eval a * w.eval a -
      (2 : k) * (p.coeff 2).eval a * w.derivative.eval a = 0 := by
  have hrow := eighthCoefficientJacobianRow_68 hp hq hjac
  have heval := congrArg (fun f : k[X] => f.eval a) hrow
  simp [hp6, hq8, hp5, hp4, hq7, hq6, hq5, hq4,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, eval_add, eval_sub, eval_mul, eval_pow, eval_C,
    eval_zero, ha] at heval
  linear_combination heval

/-- Structural obstruction: on the surviving `r ≠ 0` cubic core the
degree-five row always has a unique choice of the fresh `q₂(a)` coordinate.
Consequently this row, without a separate second-order integrated-`T` or
support condition, cannot force `r=0`. -/
theorem degreeFive_cubicCore_q2_solvable_68
    (d r p1 u p3 p3' q3 q3' p2 p2' w w' : k)
    (hd : d ≠ 0) (hr : r ≠ 0) :
    ∃ q2 : k,
      d * ((2 : k) * (r ^ 2 / 3) * q2 - p1 * u) +
        3 * (p3' * q3 - p3 * q3') + 4 * p2' * w - 2 * p2 * w' = 0 := by
  have hden : (2 : k) * d * (r ^ 2 / 3) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hd)
      (div_ne_zero (pow_ne_zero 2 hr) (by norm_num))
  refine ⟨(d * p1 * u - 3 * (p3' * q3 - p3 * q3') -
      4 * p2' * w + 2 * p2 * w') / ((2 : k) * d * (r ^ 2 / 3)), ?_⟩
  field_simp [hden]
  ring

end DegreeFiveRow68

end Max11DegreeRoutes
