import LowScale68ScaleTwoAlignedNonsquareDivisibility
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
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Cleared ninth defect of the degree-`6` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
the fifth defect `F`, the sixth defect `G`, the seventh defect `I`,
and the eighth defect `J`.  On the aligned face it is a polynomial
first integral of weight `45/2`. -/
def alignedNinthDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (1813985280 : K[X]) * a0 * a3 * H ^ 21 + (1813985280 : K[X]) * a1 * a2 * H
    ^ 21 - (1632586752 : K[X]) * b1 * H ^ 22 - (604661760 : K[X]) * a0 * a4
    * a5 * H ^ 18 - (604661760 : K[X]) * a1 * a3 * a5 * H ^ 18 - (302330880
    : K[X]) * a1 * a4 ^ 2 * H ^ 18 - (302330880 : K[X]) * a2 ^ 2 * a5 * H ^
    18 - (604661760 : K[X]) * a2 * a3 * a4 * H ^ 18 - (100776960 : K[X]) *
    a3 ^ 3 * H ^ 18 + (134369280 : K[X]) * a0 * a5 ^ 3 * H ^ 15 + (403107840
    : K[X]) * a1 * a4 * a5 ^ 2 * H ^ 15 + (403107840 : K[X]) * a2 * a3 * a5
    ^ 2 * H ^ 15 + (403107840 : K[X]) * a2 * a4 ^ 2 * a5 * H ^ 15 +
    (403107840 : K[X]) * a3 ^ 2 * a4 * a5 * H ^ 15 + (134369280 : K[X]) * a3
    * a4 ^ 3 * H ^ 15 - (78382080 : K[X]) * a1 * a5 ^ 4 * H ^ 12 -
    (313528320 : K[X]) * a2 * a4 * a5 ^ 3 * H ^ 12 - (156764160 : K[X]) * a3
    ^ 2 * a5 ^ 3 * H ^ 12 - (470292480 : K[X]) * a3 * a4 ^ 2 * a5 ^ 2 * H ^
    12 - (78382080 : K[X]) * a4 ^ 4 * a5 * H ^ 12 + (52254720 : K[X]) * a2 *
    a5 ^ 5 * H ^ 9 + (261273600 : K[X]) * a3 * a4 * a5 ^ 4 * H ^ 9 +
    (174182400 : K[X]) * a4 ^ 3 * a5 ^ 3 * H ^ 9 - (37739520 : K[X]) * a3 *
    a5 ^ 6 * H ^ 6 - (113218560 : K[X]) * a4 ^ 2 * a5 ^ 5 * H ^ 6 +
    (28753920 : K[X]) * a4 * a5 ^ 7 * H ^ 3 - (2529280 : K[X]) * a5 ^ 9 +
    Polynomial.C κ * ((80621568 : K[X]) * a0 * a5 * H ^ 20 + (80621568 :
    K[X]) * a1 * a4 * H ^ 20 + (80621568 : K[X]) * a2 * a3 * H ^ 20 -
    (26873856 : K[X]) * a1 * a5 ^ 2 * H ^ 17 - (53747712 : K[X]) * a2 * a4 *
    a5 * H ^ 17 - (26873856 : K[X]) * a3 ^ 2 * a5 * H ^ 17 - (26873856 :
    K[X]) * a3 * a4 ^ 2 * H ^ 17 + (14929920 : K[X]) * a2 * a5 ^ 3 * H ^ 14
    + (44789760 : K[X]) * a3 * a4 * a5 ^ 2 * H ^ 14 + (14929920 : K[X]) * a4
    ^ 3 * a5 * H ^ 14 - (9953280 : K[X]) * a3 * a5 ^ 4 * H ^ 11 - (19906560
    : K[X]) * a4 ^ 2 * a5 ^ 3 * H ^ 11 + (7299072 : K[X]) * a4 * a5 ^ 5 * H
    ^ 8 - (811008 : K[X]) * a5 ^ 7 * H ^ 5) - ((23514624 : K[X]) * a0 * H ^
    15 + (3919104 : K[X]) * a1 * a5 * H ^ 12 + (3919104 : K[X]) * a2 * a4 *
    H ^ 12 + (1959552 : K[X]) * a3 ^ 2 * H ^ 12 - (1632960 : K[X]) * a2 * a5
    ^ 2 * H ^ 9 - (3265920 : K[X]) * a3 * a4 * a5 * H ^ 9 - (544320 : K[X])
    * a4 ^ 3 * H ^ 9 + (997920 : K[X]) * a3 * a5 ^ 3 * H ^ 6 + (1496880 :
    K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 6 - (706860 : K[X]) * a4 * a5 ^ 4 * H ^ 3
    + (90321 : K[X]) * a5 ^ 6) * alignedThirdDefect610 H a3 a4 a5 b7 κ -
    (3359232 : K[X]) * a1 * H ^ 12 * alignedFourthDefect610 H a2 a3 a4 a5 b6
    b7 κ - ((233280 : K[X]) * a2 * H ^ 9 - (38880 : K[X]) * a3 * a5 * H ^ 6
    - (19440 : K[X]) * a4 ^ 2 * H ^ 6 + (22680 : K[X]) * a4 * a5 ^ 2 * H ^ 3
    - (4095 : K[X]) * a5 ^ 4) * alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6
    b7 κ - ((10368 : K[X]) * a3 * H ^ 6 - (3456 : K[X]) * a4 * a5 * H ^ 3 +
    (768 : K[X]) * a5 ^ 3) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5
    b6 b7 κ - ((324 : K[X]) * a4 * H ^ 3 - (81 : K[X]) * a5 ^ 2) *
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - (36 :
    K[X]) * a5 * alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6
    b7 κ

end Max11DegreeRoutes
