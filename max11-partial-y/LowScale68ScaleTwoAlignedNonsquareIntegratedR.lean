import LowScale68ScaleTwoAlignedNonsquareIntegratedQ

/-! # First divided row after integrated Q in the aligned nonsquare lane -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section IntegratedRAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- Clearing the integrated `R` identity in the degree-eight quotient box. -/
theorem integratedR_degreeEight_b4_shape_68
    (h center r t v a2 s u b4 alpha gamma : F) (hh : h ≠ 0)
    (hcenter : center = r / (6 * h))
    (hR : depressedR68 h center ((4 / 3 : F) * h ^ 6 * r)
        (h ^ 4 * s) (h ^ 2 * u) b4 =
      integratedR68 0
        (depressedA68 h center (h ^ 4 * r) (h ^ 2 * t))
        (depressedB68 h center (h ^ 4 * r) (h ^ 2 * t) v)
        (depressedC68 h center (h ^ 4 * r) (h ^ 2 * t) v a2)
        alpha gamma) :
    b4 + (5 / 12 : F) * s * r ^ 2 - (5 / 6 : F) * u * r -
        (35 / 216 : F) * r ^ 4 =
      (4 / 3 : F) *
          (h ^ 2 * a2 - (1 / 2 : F) * v * r +
            (1 / 6 : F) * t * r ^ 2 - (5 / 144 : F) * r ^ 4) +
        (2 / 9 : F) * (t - (5 / 12 : F) * r ^ 2) ^ 2 +
        alpha * h ^ 2 * (t - (5 / 12 : F) * r ^ 2) +
        gamma * h ^ 4 := by
  subst center
  calc
    b4 + (5 / 12 : F) * s * r ^ 2 - (5 / 6 : F) * u * r -
        (35 / 216 : F) * r ^ 4 =
        h ^ 4 * depressedR68 h (r / (6 * h))
          ((4 / 3 : F) * h ^ 6 * r) (h ^ 4 * s) (h ^ 2 * u) b4 := by
      simp only [depressedR68]
      field_simp [hh]
      ring
    _ = h ^ 4 * integratedR68 0
        (depressedA68 h (r / (6 * h)) (h ^ 4 * r) (h ^ 2 * t))
        (depressedB68 h (r / (6 * h)) (h ^ 4 * r) (h ^ 2 * t) v)
        (depressedC68 h (r / (6 * h)) (h ^ 4 * r) (h ^ 2 * t) v a2)
        alpha gamma := by rw [hR]
    _ = (4 / 3 : F) *
          (h ^ 2 * a2 - (1 / 2 : F) * v * r +
            (1 / 6 : F) * t * r ^ 2 - (5 / 144 : F) * r ^ 4) +
        (2 / 9 : F) * (t - (5 / 12 : F) * r ^ 2) ^ 2 +
        alpha * h ^ 2 * (t - (5 / 12 : F) * r ^ 2) +
        gamma * h ^ 4 := by
      simp only [integratedR68, depressedA68, depressedB68, depressedC68,
        zero_mul, add_zero]
      field_simp [hh]
      ring

/-- The root specialization of cleared integrated `R`. -/
theorem integratedR_degreeEight_root_shape_68
    (r t v s u w : F)
    (hsecond : (9 : F) * s = 2 * r ^ 2 + 12 * t)
    (hQ : u = (4 / 3 : F) * v + s * r - (8 / 9 : F) * t * r -
      (22 / 81 : F) * r ^ 3)
    (hR : w + (5 / 12 : F) * s * r ^ 2 - (5 / 6 : F) * u * r -
        (35 / 216 : F) * r ^ 4 =
      (4 / 3 : F) * (-(1 / 2 : F) * v * r +
          (1 / 6 : F) * t * r ^ 2 - (5 / 144 : F) * r ^ 4) +
        (2 / 9 : F) * (t - (5 / 12 : F) * r ^ 2) ^ 2)
    (hrow : 8 * r * w + t * u - 6 * v * s = 0) :
    (3 * t - r ^ 2) * (2 * r ^ 3 - 9 * r * t + 27 * v) = 0 := by
  linear_combination
    ((169 / 40 : F) * r ^ 3 + (9 / 20 : F) * r * t +
        (81 / 80 : F) * r * s - (27 / 4 : F) * v -
        (81 / 80 : F) * u) * hsecond +
      ((3159 / 40 : F) * r ^ 2 + (729 / 80 : F) * s) * hQ +
      ((486 / 5 : F) * r) * hR + (-243 / 20 : F) * hrow

end IntegratedRAlgebra68

section DividedDegreeEightRow68

variable {k : Type*} [Field k] [CharZero k]

/-- Differentiating the raw degree-eight row once extracts its first
nonzero quotient at a simple root of the quadratic core. -/
theorem fifthCoefficientJacobianRow_divided_eval_root_68
    {p q : k[X][Y]} {j : k} {H r t s u w : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hp5 : p.coeff 5 = H ^ 2 * r)
    (hp4 : p.coeff 4 = H * t)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * H ^ 3 * r)
    (hq6 : q.coeff 6 = H ^ 2 * s)
    (hq5 : q.coeff 5 = H * u)
    (hq4 : q.coeff 4 = w)
    (ha : H.eval a = 0) (hH' : H.derivative.eval a ≠ 0) :
    (8 : k) * r.eval a * w.eval a + t.eval a * u.eval a -
        (6 : k) * (p.coeff 3).eval a * s.eval a = 0 := by
  have hrow := fifthCoefficientJacobianRow_68 hp hq hjac
  have hder := congrArg (fun f : k[X] => f.derivative.eval a) hrow
  simp [hp6, hq8, hp5, hp4, hq7, hq6, hq5, hq4,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, eval_add, eval_sub, eval_mul, eval_pow, eval_C,
    eval_zero, ha] at hder
  have hfactor : (H.derivative.eval a) ^ 2 *
      ((8 : k) * r.eval a * w.eval a + t.eval a * u.eval a -
        (6 : k) * (p.coeff 3).eval a * s.eval a) = 0 := by
    linear_combination hder
  exact (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero 2 hH')

end DividedDegreeEightRow68

end Max11DegreeRoutes
