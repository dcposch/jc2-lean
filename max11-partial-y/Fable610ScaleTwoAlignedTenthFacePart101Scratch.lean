import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch
import Fable610ScaleTwoAlignedNinthFacePart101Scratch
import Fable610ScaleTwoAlignedFlatDefectPart101Scratch
import Fable610ScaleTwoAlignedFlatDefectPart102Scratch
import Fable610ScaleTwoAlignedFlatDefectPart103Scratch
import Fable610ScaleTwoAlignedFlatDefectPart104Scratch
import Fable610ScaleTwoAlignedFlatDefectPart105Scratch
import Fable610ScaleTwoAlignedFlatDefectPart106Scratch
import Fable610ScaleTwoAlignedFlatDefectPart107Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`5` Jacobian coefficient, the first
aligned row that sees `q₀` (through `q₀'` only). -/
theorem alignedTenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC2, hC3, hC4, hC5, hC6]
  linear_combination hcoeff

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 1600000000 in
/-- Cleared tenth defect of the degree-`5` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
the fifth defect `F`, the sixth defect `G`, the seventh defect `I`,
the eighth defect `J`, and the ninth defect `L`.  On the aligned face
it is a polynomial first integral of weight `25`. -/
def alignedTenthDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
  (10883911680 : K[X]) * a0 * a2 * H ^ 24 - (3627970560 : K[X]) * a0 *
    a3 * a5 * H ^ 21 - (1813985280 : K[X]) * a0 * a4 ^ 2 * H ^ 21 +
    (2418647040 : K[X]) * a0 * a4 * a5 ^ 2 * H ^ 18 - (470292480 : K[X]) *
    a0 * a5 ^ 4 * H ^ 15 + (5441955840 : K[X]) * a1 ^ 2 * H ^ 24 -
    (3627970560 : K[X]) * a1 * a2 * a5 * H ^ 21 - (3627970560 : K[X]) * a1
    * a3 * a4 * H ^ 21 + (2418647040 : K[X]) * a1 * a3 * a5 ^ 2 * H ^ 18 +
    (2418647040 : K[X]) * a1 * a4 ^ 2 * a5 * H ^ 18 - (1881169920 : K[X])
    * a1 * a4 * a5 ^ 3 * H ^ 15 + (313528320 : K[X]) * a1 * a5 ^ 5 * H ^
    12 - (1813985280 : K[X]) * a2 ^ 2 * a4 * H ^ 21 + (1209323520 : K[X])
    * a2 ^ 2 * a5 ^ 2 * H ^ 18 - (1813985280 : K[X]) * a2 * a3 ^ 2 * H ^
    21 + (4837294080 : K[X]) * a2 * a3 * a4 * a5 * H ^ 18 - (1881169920 :
    K[X]) * a2 * a3 * a5 ^ 3 * H ^ 15 + (806215680 : K[X]) * a2 * a4 ^ 3 *
    H ^ 18 - (2821754880 : K[X]) * a2 * a4 ^ 2 * a5 ^ 2 * H ^ 15 +
    (1567641600 : K[X]) * a2 * a4 * a5 ^ 4 * H ^ 12 - (226437120 : K[X]) *
    a2 * a5 ^ 6 * H ^ 9 + (806215680 : K[X]) * a3 ^ 3 * a5 * H ^ 18 +
    (1209323520 : K[X]) * a3 ^ 2 * a4 ^ 2 * H ^ 18 - (2821754880 : K[X]) *
    a3 ^ 2 * a4 * a5 ^ 2 * H ^ 15 + (783820800 : K[X]) * a3 ^ 2 * a5 ^ 4 *
    H ^ 12 - (1881169920 : K[X]) * a3 * a4 ^ 3 * a5 * H ^ 15 + (3135283200
    : K[X]) * a3 * a4 ^ 2 * a5 ^ 3 * H ^ 12 - (1358622720 : K[X]) * a3 *
    a4 * a5 ^ 5 * H ^ 9 + (172523520 : K[X]) * a3 * a5 ^ 7 * H ^ 6 -
    (94058496 : K[X]) * a4 ^ 5 * H ^ 15 + (783820800 : K[X]) * a4 ^ 4 * a5
    ^ 2 * H ^ 12 - (1132185600 : K[X]) * a4 ^ 3 * a5 ^ 4 * H ^ 9 +
    (603832320 : K[X]) * a4 ^ 2 * a5 ^ 6 * H ^ 6 - (136581120 : K[X]) * a4
    * a5 ^ 8 * H ^ 3 + (11128832 : K[X]) * a5 ^ 10 - (9795520512 : K[X]) *
    b0 * H ^ 25 + Polynomial.C κ * ((483729408 : K[X]) * a0 * a4 * H ^ 23
    - (161243136 : K[X]) * a0 * a5 ^ 2 * H ^ 20 + (483729408 : K[X]) * a1
    * a3 * H ^ 23 - (322486272 : K[X]) * a1 * a4 * a5 * H ^ 20 + (89579520
    : K[X]) * a1 * a5 ^ 3 * H ^ 17 + (241864704 : K[X]) * a2 ^ 2 * H ^ 23
    - (322486272 : K[X]) * a2 * a3 * a5 * H ^ 20 - (161243136 : K[X]) * a2
    * a4 ^ 2 * H ^ 20 + (268738560 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 17 -
    (59719680 : K[X]) * a2 * a5 ^ 4 * H ^ 14 - (161243136 : K[X]) * a3 ^ 2
    * a4 * H ^ 20 + (134369280 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 17 +
    (268738560 : K[X]) * a3 * a4 ^ 2 * a5 * H ^ 17 - (238878720 : K[X]) *
    a3 * a4 * a5 ^ 3 * H ^ 14 + (43794432 : K[X]) * a3 * a5 ^ 5 * H ^ 11 +
    (22394880 : K[X]) * a4 ^ 4 * H ^ 17 - (119439360 : K[X]) * a4 ^ 3 * a5
    ^ 2 * H ^ 14 + (109486080 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 11 -
    (34062336 : K[X]) * a4 * a5 ^ 6 * H ^ 8 + (3446784 : K[X]) * a5 ^ 8 *
    H ^ 5) - ((23514624 : K[X]) * a0 * a5 * H ^ 15 + (23514624 : K[X]) *
    a1 * a4 * H ^ 15 - (9797760 : K[X]) * a1 * a5 ^ 2 * H ^ 12 + (23514624
    : K[X]) * a2 * a3 * H ^ 15 - (19595520 : K[X]) * a2 * a4 * a5 * H ^ 12
    + (5987520 : K[X]) * a2 * a5 ^ 3 * H ^ 9 - (9797760 : K[X]) * a3 ^ 2 *
    a5 * H ^ 12 - (9797760 : K[X]) * a3 * a4 ^ 2 * H ^ 12 + (17962560 :
    K[X]) * a3 * a4 * a5 ^ 2 * H ^ 9 - (4241160 : K[X]) * a3 * a5 ^ 4 * H
    ^ 6 + (5987520 : K[X]) * a4 ^ 3 * a5 * H ^ 9 - (8482320 : K[X]) * a4 ^
    2 * a5 ^ 3 * H ^ 6 + (3251556 : K[X]) * a4 * a5 ^ 5 * H ^ 3 - (374187
    : K[X]) * a5 ^ 7) * alignedThirdDefect610 H a3 a4 a5 b7 κ - ((20155392
    : K[X]) * a0 * H ^ 15) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ
    - ((1399680 : K[X]) * a1 * H ^ 12 - (233280 : K[X]) * a2 * a5 * H ^ 9
    - (233280 : K[X]) * a3 * a4 * H ^ 9 + (136080 : K[X]) * a3 * a5 ^ 2 *
    H ^ 6 + (136080 : K[X]) * a4 ^ 2 * a5 * H ^ 6 - (98280 : K[X]) * a4 *
    a5 ^ 3 * H ^ 3 + (15561 : K[X]) * a5 ^ 5) * alignedFifthDefect610 H a1
    a2 a3 a4 a5 b5 b6 b7 κ - ((62208 : K[X]) * a2 * H ^ 9 - (20736 : K[X])
    * a3 * a5 * H ^ 6 - (10368 : K[X]) * a4 ^ 2 * H ^ 6 + (13824 : K[X]) *
    a4 * a5 ^ 2 * H ^ 3 - (2688 : K[X]) * a5 ^ 4) * alignedSixthDefect610
    H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ - ((1944 : K[X]) * a3 * H ^ 6 - (972
    : K[X]) * a4 * a5 * H ^ 3 + (243 : K[X]) * a5 ^ 3) *
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - ((216 :
    K[X]) * a4 * H ^ 3 - (72 : K[X]) * a5 ^ 2) * alignedEighthDefect610 H
    a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ - a5 * alignedNinthDefect610 H
    a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Peeled square-chamber form of the consumed degree-`5` row
(`h₀⁴⁰ · h₀² · h₀ · h₀` cancelled along the seventh-face
divisibilities, the eighth-face product divisor `u₂`, and the NEW
μ-loaded divisor `s₂`): head seeing `p₂`, `q₀` tied at `h₀⁶`.  On the
face it equals `κ₉ h₀⁶`. -/
def alignedTenthSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 u2 s2 a0 a1 a2 b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  ((184320 : K[X]) * e1 ^ 2 * e2 ^ 2 + (737280 : K[X]) * e1 ^ 2 * u2 *
    w1 ^ 2 - (44789760 : K[X]) * e1 ^ 2 * w1 ^ 2 * a2 + (40960 : K[X]) *
    e2 ^ 2 * u2 - (2488320 : K[X]) * e2 ^ 2 * a2 + (92160 : K[X]) * u2 ^ 2
    * w1 ^ 2 - (14929920 : K[X]) * u2 * w1 ^ 2 * a2 - (135 : K[X]) * s2 +
    (604661760 : K[X]) * w1 ^ 2 * a2 ^ 2 + Polynomial.C μ * ((2268 : K[X])
    * e1 * w1 ^ 5)) + h0 * (-((387072 : K[X]) * e1 ^ 5) - (2580480 : K[X])
    * e1 ^ 3 * u2 + (29859840 : K[X]) * e1 ^ 3 * a2 - (798720 : K[X]) * e1
    * u2 ^ 2 + (59719680 : K[X]) * e1 * u2 * a2 - (604661760 : K[X]) * e1
    * a2 ^ 2 - Polynomial.C ν * ((81 : K[X]) * w1 ^ 5) + Polynomial.C μ *
    ((15120 : K[X]) * e1 ^ 2 * w1 ^ 3) + Polynomial.C μ * ((2520 : K[X]) *
    u2 * w1 ^ 3) - Polynomial.C μ * ((326592 : K[X]) * w1 ^ 3 * a2) -
    Polynomial.C κ * ((73728 : K[X]) * e1 * e2 ^ 2) - Polynomial.C κ *
    ((221184 : K[X]) * e1 * u2 * w1 ^ 2) + Polynomial.C κ * ((17915904 :
    K[X]) * e1 * w1 ^ 2 * a2)) + h0 ^ 2 * ((268738560 : K[X]) * e1 ^ 2 *
    w1 * a1 - (44789760 : K[X]) * e1 * e2 * a1 + (44789760 : K[X]) * u2 *
    w1 * a1 - (3627970560 : K[X]) * w1 * a1 * a2 - Polynomial.C ν * ((1080
    : K[X]) * e1 * w1 ^ 3) - Polynomial.C μ * ((221760 : K[X]) * e1 ^ 3 *
    w1) + Polynomial.C μ * ((40320 : K[X]) * e1 ^ 2 * e2) - Polynomial.C μ
    * ((100800 : K[X]) * e1 * u2 * w1) + Polynomial.C μ * ((6531840 :
    K[X]) * e1 * w1 * a2) + Polynomial.C μ * ((13440 : K[X]) * e2 * u2) -
    Polynomial.C μ * ((870912 : K[X]) * e2 * a2) + Polynomial.C κ *
    ((276480 : K[X]) * e1 ^ 4) + Polynomial.C κ * ((1105920 : K[X]) * e1 ^
    2 * u2) - Polynomial.C κ * ((17915904 : K[X]) * e1 ^ 2 * a2) +
    Polynomial.C κ * ((110592 : K[X]) * u2 ^ 2) - Polynomial.C κ *
    ((11943936 : K[X]) * u2 * a2) + Polynomial.C κ * ((241864704 : K[X]) *
    a2 ^ 2)) + h0 ^ 3 * (Polynomial.C ν₂ * ((9 : K[X]) * w1 ^ 3) -
    Polynomial.C ν * ((15120 : K[X]) * e1 ^ 2 * w1) + Polynomial.C ν *
    ((2880 : K[X]) * e1 * e2) - Polynomial.C ν * ((2160 : K[X]) * u2 * w1)
    + Polynomial.C ν * ((233280 : K[X]) * w1 * a2) + Polynomial.C μ *
    ((1959552 : K[X]) * w1 ^ 2 * a1) - Polynomial.C κ * ((107495424 :
    K[X]) * e1 * w1 * a1) + Polynomial.C κ * ((17915904 : K[X]) * e2 *
    a1)) + h0 ^ 4 * (-((201553920 : K[X]) * e1 ^ 2 * a0) - (134369280 :
    K[X]) * u2 * a0 + (10883911680 : K[X]) * a0 * a2 + (5441955840 : K[X])
    * a1 ^ 2 + Polynomial.C ν₂ * ((324 : K[X]) * e1 * w1) - Polynomial.C
    ν₂ * ((72 : K[X]) * e2) + Polynomial.C κ₅ * ((1152 : K[X]) * e1 ^ 2) +
    Polynomial.C κ₅ * ((768 : K[X]) * u2) - Polynomial.C κ₅ * ((62208 :
    K[X]) * a2) - Polynomial.C μ * ((7838208 : K[X]) * e1 * a1)) + h0 ^ 5
    * (-(Polynomial.C μ₃ * (w1)) - Polynomial.C κ₇ * ((72 : K[X]) * e1) -
    Polynomial.C ν * ((1399680 : K[X]) * a1) - Polynomial.C μ * ((23514624
    : K[X]) * w1 * a0) + Polynomial.C κ * ((161243136 : K[X]) * e1 * a0))
    + h0 ^ 6 * (-((9795520512 : K[X]) * b0) - Polynomial.C κ₃ * ((20155392
    : K[X]) * a0))

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Scalar resolution of the tenth-row peeled head at the root against
`e₂(a) = 0` and the `u₂` root product: with `x (v - 3 u x) = 0` and
`v = 0`, the head equation forces the exact tie
`135 s = 92160 x² (81 p - y)²` — the carried `p₂`-block has
perfect-square discriminant. -/
theorem alignedTenthSquareTieResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v y p s m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : v = 0)
    (hhead : 184320 * u ^ 2 * v ^ 2 - 44789760 * u ^ 2 * p * x ^ 2 +
      737280 * u ^ 2 * y * x ^ 2 + 2268 * u * m * x ^ 5 -
      2488320 * v ^ 2 * p + 40960 * v ^ 2 * y +
      604661760 * p ^ 2 * x ^ 2 - 14929920 * p * y * x ^ 2 -
      135 * s + 92160 * y ^ 2 * x ^ 2 = 0) :
    135 * s = 92160 * x ^ 2 * (81 * p - y) ^ 2 := by
  have hux2 : u * x ^ 2 = 0 := by
    linear_combination (-(3 : K)⁻¹) * h1 + ((3 : K)⁻¹ * x) * h2
  have hux : u * x = 0 := by
    rcases mul_eq_zero.mp hux2 with hu | hx2
    · rw [hu, zero_mul]
    · rw [(pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx2, mul_zero]
  linear_combination -hhead +
    (2268 * m * x ^ 4 - 44789760 * p * u * x + 737280 * u * x * y) *
      hux +
    (-2488320 * p * v + 184320 * u ^ 2 * v + 40960 * v * y) * h2

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Solved block of the nonsquare tenth row after the carried
`u`- and `t₃`-substitutions and the NEW `v`-substitution peel the last
three powers of `H`: `9795520512 q₀` equals this block minus `κ₉` —
the constant enters at level ZERO. -/
def alignedTenthNonsquareSolved610 {K : Type*} [CommRing K]
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) : K[X] :=
  (-((387072 : K[X]) * t1 ^ 5) + (368640 : K[X]) * t1 ^ 3 * u -
    (201553920 : K[X]) * t1 ^ 2 * a0 - (92160 : K[X]) * t1 * u ^ 2 +
    (134369280 : K[X]) * u * a0 - Polynomial.C κ₇ * ((72 : K[X]) * t1) +
    Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) - Polynomial.C κ₅ * ((768 :
    K[X]) * u) - Polynomial.C κ₃ * ((20155392 : K[X]) * a0) + Polynomial.C
    κ * ((276480 : K[X]) * t1 ^ 4) - Polynomial.C κ * ((221184 : K[X]) *
    t1 ^ 2 * u) + Polynomial.C κ * ((161243136 : K[X]) * t1 * a0) +
    Polynomial.C κ * ((36864 : K[X]) * u ^ 2)) + H * ((184320 : K[X]) * t1
    ^ 2 * t3 ^ 2 - (184320 : K[X]) * t1 * t3 * v - (30720 : K[X]) * u * t3
    ^ 2 + (10240 : K[X]) * t3 ^ 3 * g1 + (92160 : K[X]) * v ^ 2 -
    Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) + Polynomial.C κ *
    ((73728 : K[X]) * t3 * v))

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart101Scratch in
open private memory610_flatFourthDefect from Fable610ScaleTwoAlignedFlatDefectPart102Scratch in
open private memory610_flatFifthDefect from Fable610ScaleTwoAlignedFlatDefectPart103Scratch in
open private memory610_flatSixthDefect from Fable610ScaleTwoAlignedFlatDefectPart104Scratch in
open private memory610_flatSeventhDefect from Fable610ScaleTwoAlignedFlatDefectPart105Scratch in
open private memory610_flatEighthDefect from Fable610ScaleTwoAlignedFlatDefectPart106Scratch in
open private memory610_flatNinthDefect from Fable610ScaleTwoAlignedFlatDefectPart107Scratch in
set_option maxHeartbeats 8000000000 in
/-- Exact combination of the degree-`5` Jacobian expression with the
weighted derivative of `Ω`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` through
degree-`6` rows.  The row sees neither `q₉` nor `q₈`, so there is no
`N`-correction and no `C`-correction — the source-correction module is
EMPTY, as for the ninth face. -/
theorem alignedTenthDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (1632586752 : K[X]) * H ^ 23 * (a5.derivative * b1 + a4.derivative *
      (b2 * (2 : K[X])) + a3.derivative * (b3 * (3 : K[X])) +
      a2.derivative * (b4 * (4 : K[X])) + a1.derivative * (b5 * (5 :
      K[X])) + a0.derivative * (b6 * (6 : K[X])) - ((H ^ 3 * (6 : K[X])) *
      b0.derivative + (a5 * (5 : K[X])) * b1.derivative + (a4 * (4 :
      K[X])) * b2.derivative + (a3 * (3 : K[X])) * b3.derivative + (a2 *
      (2 : K[X])) * b4.derivative + a1 * b5.derivative)) = (H *
      (alignedTenthDefect610 H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7
      κ).derivative - (25 : K[X]) * alignedTenthDefect610 H a0 a1 a2 a3 a4
      a5 b0 b1 b2 b3 b4 b5 b6 b7 κ * H.derivative) + ((70543872 : K[X]) *
      a0 * a5 * H ^ 15 + (70543872 : K[X]) * a1 * a4 * H ^ 15 + (5878656 :
      K[X]) * a1 * a5 ^ 2 * H ^ 12 + (70543872 : K[X]) * a2 * a3 * H ^ 15
      + (11757312 : K[X]) * a2 * a4 * a5 * H ^ 12 - (1632960 : K[X]) * a2
      * a5 ^ 3 * H ^ 9 + (5878656 : K[X]) * a3 ^ 2 * a5 * H ^ 12 +
      (5878656 : K[X]) * a3 * a4 ^ 2 * H ^ 12 - (4898880 : K[X]) * a3 * a4
      * a5 ^ 2 * H ^ 9 + (748440 : K[X]) * a3 * a5 ^ 4 * H ^ 6 - (1632960
      : K[X]) * a4 ^ 3 * a5 * H ^ 9 + (1496880 : K[X]) * a4 ^ 2 * a5 ^ 3 *
      H ^ 6 - (424116 : K[X]) * a4 * a5 ^ 5 * H ^ 3 + (38709 : K[X]) * a5
      ^ 7) * ((2 : K[X]) * H * (alignedThirdDefect610 H a3 a4 a5 b7
      κ).derivative - (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ
      * H.derivative) + ((20155392 : K[X]) * a0 * H ^ 15 + (20155392 :
      K[X]) * a1 * a5 * H ^ 12 + (20155392 : K[X]) * a2 * a4 * H ^ 12 +
      (10077696 : K[X]) * a3 ^ 2 * H ^ 12) * (H * (alignedFourthDefect610
      H a2 a3 a4 a5 b6 b7 κ).derivative - (10 : K[X]) *
      alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ * H.derivative) +
      ((839808 : K[X]) * a1 * H ^ 12 + (699840 : K[X]) * a2 * a5 * H ^ 9 +
      (699840 : K[X]) * a3 * a4 * H ^ 9 - (58320 : K[X]) * a3 * a5 ^ 2 * H
      ^ 6 - (58320 : K[X]) * a4 ^ 2 * a5 * H ^ 6 + (22680 : K[X]) * a4 *
      a5 ^ 3 * H ^ 3 - (2457 : K[X]) * a5 ^ 5) * ((2 : K[X]) * H *
      (alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ).derivative - (25
      : K[X]) * alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ *
      H.derivative) + ((93312 : K[X]) * a2 * H ^ 9 + (62208 : K[X]) * a3 *
      a5 * H ^ 6 + (31104 : K[X]) * a4 ^ 2 * H ^ 6 - (10368 : K[X]) * a4 *
      a5 ^ 2 * H ^ 3 + (1152 : K[X]) * a5 ^ 4) * (H *
      (alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ).derivative
      - (15 : K[X]) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6
      b7 κ * H.derivative) + ((1944 : K[X]) * a3 * H ^ 6 + (972 : K[X]) *
      a4 * a5 * H ^ 3 - (81 : K[X]) * a5 ^ 3) * ((2 : K[X]) * H *
      (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
      κ).derivative - (35 : K[X]) * alignedSeventhDefect610 H a0 a1 a2 a3
      a4 a5 b3 b4 b5 b6 b7 κ * H.derivative) + ((648 : K[X]) * a4 * H ^ 3
      + (108 : K[X]) * a5 ^ 2) * (H * (alignedEighthDefect610 H a0 a1 a2
      a3 a4 a5 b2 b3 b4 b5 b6 b7 κ).derivative - (20 : K[X]) *
      alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ *
      H.derivative) + (3 : K[X]) * a5 * ((2 : K[X]) * H *
      (alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
      κ).derivative - (45 : K[X]) * alignedNinthDefect610 H a0 a1 a2 a3 a4
      a5 b1 b2 b3 b4 b5 b6 b7 κ * H.derivative) := by
  simp only [alignedTenthDefect610, memory610_flatNinthDefect, memory610_flatEighthDefect, memory610_flatSeventhDefect, memory610_flatSixthDefect, memory610_flatFifthDefect, memory610_flatFourthDefect, memory610_flatThirdDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_neg, Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul, zero_mul, mul_zero, zero_add, add_zero, neg_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_zero]
  ring

end Max11DegreeRoutes
