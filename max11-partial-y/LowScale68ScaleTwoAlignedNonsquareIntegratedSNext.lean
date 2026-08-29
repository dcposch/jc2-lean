import LowScale68ScaleTwoAlignedNonsquareIntegratedR

/-! # Source integrated R and next Keller row in the nonsquare lane -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section NextRow68

variable {k : Type*} [Field k] [CharZero k]

/-- The next, degree-seven coefficient of the literal Keller bracket. -/
theorem sixthCoefficientJacobianRow_68 {p q : k[X][Y]} {j : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j)) :
    (p.coeff 6).derivative * (q.coeff 2 * C (2 : k)) +
        (p.coeff 5).derivative * (q.coeff 3 * C (3 : k)) +
        (p.coeff 4).derivative * (q.coeff 4 * C (4 : k)) +
        (p.coeff 3).derivative * (q.coeff 5 * C (5 : k)) +
        (p.coeff 2).derivative * (q.coeff 6 * C (6 : k)) +
        (p.coeff 1).derivative * (q.coeff 7 * C (7 : k)) +
        (p.coeff 0).derivative * (q.coeff 8 * C (8 : k)) -
      ((p.coeff 6 * C (6 : k)) * (q.coeff 2).derivative +
        (p.coeff 5 * C (5 : k)) * (q.coeff 3).derivative +
        (p.coeff 4 * C (4 : k)) * (q.coeff 4).derivative +
        (p.coeff 3 * C (3 : k)) * (q.coeff 5).derivative +
        (p.coeff 2 * C (2 : k)) * (q.coeff 6).derivative +
        (p.coeff 1 * C (1 : k)) * (q.coeff 7).derivative) = 0 := by
  have hcoeff := congrArg (fun z : k[X][Y] => z.coeff 7) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (7 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 7 :
      Finset (ℕ × ℕ)) =
      ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
        (6, 1), (7, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : C (2 : k) = (2 : k[X]) := C_eq_natCast 2
  have hC3 : C (3 : k) = (3 : k[X]) := C_eq_natCast 3
  have hC4 : C (4 : k) = (4 : k[X]) := C_eq_natCast 4
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC7 : C (7 : k) = (7 : k[X]) := C_eq_natCast 7
  have hC8 : C (8 : k) = (8 : k[X]) := C_eq_natCast 8
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8]
  linear_combination hcoeff

/-- At a simple core root the degree-seven row is the sparse relation
`4tw-3vu=0`. -/
theorem sixthCoefficientJacobianRow_eval_root_68
    {p q : k[X][Y]} {j : k} {H r t s u w : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hp5 : p.coeff 5 = H ^ 2 * r) (hp4 : p.coeff 4 = H * t)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * H ^ 3 * r)
    (hq6 : q.coeff 6 = H ^ 2 * s) (hq5 : q.coeff 5 = H * u)
    (hq4 : q.coeff 4 = w)
    (ha : H.eval a = 0) (hH' : H.derivative.eval a ≠ 0) :
    (4 : k) * t.eval a * w.eval a -
        (3 : k) * (p.coeff 3).eval a * u.eval a = 0 := by
  have hrow := sixthCoefficientJacobianRow_68 hp hq hjac
  have heval := congrArg (fun f : k[X] => f.eval a) hrow
  simp [hp6, hq8, hp5, hp4, hq7, hq6, hq5, hq4,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, eval_add, eval_sub, eval_mul, eval_pow, eval_C,
    eval_zero, ha] at heval
  have hfactor : H.derivative.eval a *
      ((4 : k) * t.eval a * w.eval a -
        (3 : k) * (p.coeff 3).eval a * u.eval a) = 0 := by
    linear_combination heval
  exact (mul_eq_zero.mp hfactor).resolve_left hH'

end NextRow68

section CubicCoreAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- The integrated-Q/R packet plus the two consecutive Keller rows collapses
both former components to the same cubic core. -/
theorem integratedR_nextRow_cubicCore_68
    (r t v s u w : F)
    (hsecond : (9 : F) * s = 2 * r ^ 2 + 12 * t)
    (hQ : u = (4 / 3 : F) * v + s * r - (8 / 9 : F) * t * r -
      (22 / 81 : F) * r ^ 3)
    (hR : w + (5 / 12 : F) * s * r ^ 2 - (5 / 6 : F) * u * r -
        (35 / 216 : F) * r ^ 4 =
      (4 / 3 : F) * (-(1 / 2 : F) * v * r +
          (1 / 6 : F) * t * r ^ 2 - (5 / 144 : F) * r ^ 4) +
        (2 / 9 : F) * (t - (5 / 12 : F) * r ^ 2) ^ 2)
    (hrow8 : 8 * r * w + t * u - 6 * v * s = 0)
    (hrow7 : 4 * t * w - 3 * v * u = 0) :
    3 * t = r ^ 2 ∧ 27 * v = r ^ 3 := by
  have heS : 9 * s - 2 * r ^ 2 - 12 * t = 0 := by
    linear_combination hsecond
  have heQ : u - ((4 / 3 : F) * v + s * r - (8 / 9 : F) * t * r -
      (22 / 81 : F) * r ^ 3) = 0 := by
    linear_combination hQ
  have heR : w + (5 / 12 : F) * s * r ^ 2 - (5 / 6 : F) * u * r -
      (35 / 216 : F) * r ^ 4 -
      ((4 / 3 : F) * (-(1 / 2 : F) * v * r +
          (1 / 6 : F) * t * r ^ 2 - (5 / 144 : F) * r ^ 4) +
        (2 / 9 : F) * (t - (5 / 12 : F) * r ^ 2) ^ 2) = 0 := by
    linear_combination hR
  have hsplit := integratedR_degreeEight_root_shape_68 r t v s u w
    hsecond hQ hR hrow8
  rcases mul_eq_zero.mp hsplit with hfirst | hsecondComponent
  · have hsquare : (r ^ 3 - 27 * v) ^ 2 = 0 := by
      linear_combination
        ((23 / 12 : F) * r ^ 2 * s - (3 / 2 : F) * t ^ 2 -
            (171 / 4 : F) * r * v - (37 / 8 : F) * t * s +
            (3 / 2 : F) * r * u - (9 / 2 : F) * w) *
              heS +
          ((81 / 4 : F) * r * s - (2187 / 4 : F) * v) *
              heQ +
          ((81 / 2 : F) * s) * heR +
          ((27 : F) * r) * hrow8 +
          (-729 / 4 : F) * hrow7 +
          (-(r ^ 4) - 3 * r ^ 2 * t - (55 / 12 : F) * r ^ 2 * s -
            6 * t ^ 2 - 9 * r * v - 11 * t * s +
            (111 / 8 : F) * s ^ 2 - 3 * r * u + 225 * w) *
              hfirst
    have hv : r ^ 3 - 27 * v = 0 := (sq_eq_zero_iff).mp hsquare
    constructor
    · linear_combination hfirst
    · exact (sub_eq_zero.mp hv).symm
  · have hcube : (r ^ 2 - 3 * t) ^ 3 = 0 := by
      linear_combination
        ((9 / 4 : F) * r ^ 4 - (75 / 2 : F) * r ^ 2 * t +
            27 * r ^ 2 * s + 18 * t ^ 2 - (27 / 2 : F) * r * v +
            (27 / 4 : F) * r * u - 81 * w) *
              heS +
          ((81 / 4 : F) * r ^ 3 - (5103 / 8 : F) * r * t +
            (2187 / 4 : F) * r * s) *
              heQ +
          (-(1701 / 2 : F) * t + 729 * s) * heR +
          (-(81 / 4 : F) * r) * hrow8 +
          (-243 / 8 : F) * hrow7 +
          (-(33 / 2 : F) * r * t + 9 * r * s - (27 / 8 : F) * u) *
            hsecondComponent
    have hfirst' : r ^ 2 - 3 * t = 0 := by
      by_contra hn
      exact (pow_ne_zero 3 hn) hcube
    constructor
    · exact (sub_eq_zero.mp hfirst').symm
    · have hz : 27 * v - r ^ 3 = 0 := by
        linear_combination hsecondComponent - 3 * r * hfirst'
      exact sub_eq_zero.mp hz

end CubicCoreAlgebra68

end Max11DegreeRoutes
