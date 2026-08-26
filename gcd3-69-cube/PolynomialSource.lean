import RationalSource

noncomputable section

open Polynomial

universe u

/-! # Literal polynomial cube source

This module begins the remaining map from a normalized bivariate Keller
source to the exhaustive rational pole source closed in `RationalSource`.
The input is the original pair in `k[x][y]`; no Faber or pole landing is an
assumption.
-/

/-- Coefficientwise differentiation in the inner source variable `x`. -/
noncomputable def GCD369CubeSourceXDeriv
    {k : Type*} [CommRing k] (p : k[X][X]) : k[X][X] :=
  PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p)

@[simp] theorem GCD369CubeSourceXDeriv_coeff
    {k : Type*} [CommRing k] (p : k[X][X]) (n : ℕ) :
    (GCD369CubeSourceXDeriv p).coeff n = (p.coeff n).derivative := by
  rfl

/-- The coefficient-polynomial Jacobian of a bivariate pair. -/
noncomputable def GCD369CubeBivariateJacobian
    {k : Type*} [CommRing k] (p q : k[X][X]) : k[X][X] :=
  GCD369CubeSourceXDeriv p * derivative q -
    derivative p * GCD369CubeSourceXDeriv q

/-- The first row below the leading weighted-Wronskian row for outer
degrees `(6,9)`. -/
theorem GCD369CubeNextJacobianRow
    {k : Type*} [Field k] [CharZero k]
    {p q : k[X][X]} {j : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hjac : GCD369CubeBivariateJacobian p q = C (C j)) :
    (p.coeff 6).derivative * (q.coeff 8 * C (8 : k)) +
        (p.coeff 5).derivative * (q.coeff 9 * C (9 : k)) -
      ((p.coeff 6 * C (6 : k)) * (q.coeff 8).derivative +
        (p.coeff 5 * C (5 : k)) * (q.coeff 9).derivative) = 0 := by
  have hcoeff := congrArg (fun r : k[X][X] => r.coeff 13) hjac
  simp only [GCD369CubeBivariateJacobian, coeff_sub, coeff_mul,
    GCD369CubeSourceXDeriv_coeff, coeff_derivative, coeff_C,
    show (13 : ℕ) ≠ 0 by norm_num, if_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 13 :
      Finset (ℕ × ℕ)) =
      ({(0, 13), (1, 12), (2, 11), (3, 10), (4, 9), (5, 8), (6, 7),
        (7, 6), (8, 5), (9, 4), (10, 3), (11, 2), (12, 1), (13, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC8 : C (8 : k) = (8 : k[X]) := C_eq_natCast 8
  have hC9 : C (9 : k) = (9 : k[X]) := C_eq_natCast 9
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  rw [hC8, hC9, hC6, hC5]
  linear_combination hcoeff

/-- A literal normalized polynomial cube source at partial degrees `(6,9)`.
The two leading coefficients are the actual sixth and ninth powers of the
same nonzero polynomial, and the original Jacobian is a nonzero scalar. -/
structure GCD369CubePolynomialSource (k : Type u) [Field k] where
  s : k[X]
  p : k[X][X]
  q : k[X][X]
  j : k
  hs : s ≠ 0
  hj : j ≠ 0
  hp : p.natDegree = 6
  hq : q.natDegree = 9
  hp6 : p.coeff 6 = s ^ 6
  hq9 : q.coeff 9 = s ^ 9
  hjac : GCD369CubeBivariateJacobian p q = C (C j)

namespace GCD369CubePolynomialSource

/-- The rational-function image of the cube root. -/
noncomputable def sRat {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) S.s

/-- The normalized fifth sextic coefficient `A=a₅/s⁵`. -/
noncomputable def A {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (S.p.coeff 5) / S.sRat ^ 5

/-- The normalized eighth nonic coefficient `B=b₈/s⁸`. -/
noncomputable def B {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (S.q.coeff 8) / S.sRat ^ 8

/-- The denominator-cleared source row forced by the original Jacobian. -/
theorem firstRow
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    (3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
        (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
      (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
        (16 : k[X]) * S.q.coeff 8 * S.s.derivative = 0 := by
  have hrow := GCD369CubeNextJacobianRow S.hp S.hq S.hjac
  rw [S.hp6, S.hq9] at hrow
  have hC8 : C (8 : k) = (8 : k[X]) := C_eq_natCast 8
  have hC9 : C (9 : k) = (9 : k[X]) := C_eq_natCast 9
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  rw [hC8, hC9, hC6, hC5] at hrow
  have hscaled : (3 : k[X]) * S.s ^ 5 *
      ((3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
          (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
        (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
          (16 : k[X]) * S.q.coeff 8 * S.s.derivative) = 0 := by
    calc
      (3 : k[X]) * S.s ^ 5 *
          ((3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
              (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
            (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
              (16 : k[X]) * S.q.coeff 8 * S.s.derivative) =
          (S.s ^ 6).derivative * (S.q.coeff 8 * (8 : k[X])) +
            (S.p.coeff 5).derivative * (S.s ^ 9 * (9 : k[X])) -
          ((S.s ^ 6 * (6 : k[X])) * (S.q.coeff 8).derivative +
            (S.p.coeff 5 * (5 : k[X])) * (S.s ^ 9).derivative) := by
              simp only [derivative_pow, C_eq_natCast]
              ring
      _ = 0 := hrow
  exact (mul_eq_zero.mp hscaled).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero 5 S.hs))

/-- The alignment discriminator has one reduced rational presentation with
denominator `s⁸`. -/
theorem alignmentPresentation
    {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) :
    3 * S.A - 2 * S.B =
      algebraMap k[X] (RatFunc k)
          (3 * S.s ^ 3 * S.p.coeff 5 - 2 * S.q.coeff 8) /
        algebraMap k[X] (RatFunc k) (S.s ^ 8) := by
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  dsimp only [A, B, sRat]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  field_simp [hsRat]

/-- The literal first Jacobian row makes the rational alignment
discriminator derivative vanish. -/
theorem alignmentDerivative_zero
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeRatFuncDerivative (3 * S.A - 2 * S.B) = 0 := by
  let N : k[X] := 3 * S.s ^ 3 * S.p.coeff 5 - 2 * S.q.coeff 8
  let D : k[X] := S.s ^ 8
  have hD : D ≠ 0 := pow_ne_zero 8 S.hs
  have hpresentation : 3 * S.A - 2 * S.B =
      algebraMap k[X] (RatFunc k) N /
        algebraMap k[X] (RatFunc k) D := by
    exact S.alignmentPresentation
  rw [hpresentation, GCD369CubeRatFuncDerivative_div N D hD]
  have hnumerator : D * N.derivative - N * D.derivative = 0 := by
    calc
      D * N.derivative - N * D.derivative =
          S.s ^ 7 *
            ((3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
                (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
              (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
                (16 : k[X]) * S.q.coeff 8 * S.s.derivative) := by
            dsimp only [N, D]
            simp only [derivative_sub, derivative_mul, derivative_pow,
              derivative_ofNat, zero_mul, zero_add, C_eq_natCast]
            ring
      _ = 0 := by rw [S.firstRow, mul_zero]
  rw [← map_mul, ← map_mul, ← map_sub, hnumerator, map_zero, zero_div]

/-- The alignment discriminator is therefore an actual base-field
constant, derived from the literal polynomial source. -/
theorem alignmentConstant
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    ∃ delta : k, 3 * S.A - 2 * S.B = algebraMap k (RatFunc k) delta := by
  exact GCD369CubeRatFuncConstants _ S.alignmentDerivative_zero

end GCD369CubePolynomialSource

#print axioms GCD369CubeNextJacobianRow
#print axioms GCD369CubePolynomialSource.firstRow
#print axioms GCD369CubePolynomialSource.alignmentPresentation
#print axioms GCD369CubePolynomialSource.alignmentDerivative_zero
#print axioms GCD369CubePolynomialSource.alignmentConstant
