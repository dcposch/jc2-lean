import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch
import Fable610ScaleTwoAlignedNinthFacePart101Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- The eleventh row below the leading weighted-Wronskian row for
outer degrees `(6,10)`: the degree-`4` Jacobian coefficient, the first
aligned row with no `p₆`-term — the leading coefficient has left the
antidiagonal — seeing `q₀` through `q₀'` only. -/
theorem alignedEleventhCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : K)) -
      ((p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 4) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (4 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 4 :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1),
        (4, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC2, hC3, hC4, hC5]
  linear_combination hcoeff

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 1600000000 in
/-- Cleared eleventh defect of the degree-`4` aligned `(6,10)` row,
kept in factored form through the third defect `D`, the fifth defect
`F`, the sixth defect `G`, the seventh defect `I`, the eighth defect
`J`, and the ninth defect `L` — in the minimal gauge the fourth defect
`E` and the tenth defect `Ω` do not enter, and the raw head carries no
`q`-coefficient at all.  On the aligned face it is a squared
polynomial first integral of weight `55/2`. -/
def alignedEleventhDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
  ((522427760640 : K[X]) * a0 * a1 * H ^ 27 - (174142586880 : K[X]) * a0
    * a2 * a5 * H ^ 24 - (174142586880 : K[X]) * a0 * a3 * a4 * H ^ 24 +
    (116095057920 : K[X]) * a0 * a3 * a5 ^ 2 * H ^ 21 + (116095057920 :
    K[X]) * a0 * a4 ^ 2 * a5 * H ^ 21 - (90296156160 : K[X]) * a0 * a4 *
    a5 ^ 3 * H ^ 18 + (15049359360 : K[X]) * a0 * a5 ^ 5 * H ^ 15 -
    (87071293440 : K[X]) * a1 ^ 2 * a5 * H ^ 24 - (174142586880 : K[X]) *
    a1 * a2 * a4 * H ^ 24 + (116095057920 : K[X]) * a1 * a2 * a5 ^ 2 * H ^
    21 - (87071293440 : K[X]) * a1 * a3 ^ 2 * H ^ 24 + (232190115840 :
    K[X]) * a1 * a3 * a4 * a5 * H ^ 21 - (90296156160 : K[X]) * a1 * a3 *
    a5 ^ 3 * H ^ 18 + (38698352640 : K[X]) * a1 * a4 ^ 3 * H ^ 21 -
    (135444234240 : K[X]) * a1 * a4 ^ 2 * a5 ^ 2 * H ^ 18 + (75246796800 :
    K[X]) * a1 * a4 * a5 ^ 4 * H ^ 15 - (10868981760 : K[X]) * a1 * a5 ^ 6
    * H ^ 12 - (87071293440 : K[X]) * a2 ^ 2 * a3 * H ^ 24 + (116095057920
    : K[X]) * a2 ^ 2 * a4 * a5 * H ^ 21 - (45148078080 : K[X]) * a2 ^ 2 *
    a5 ^ 3 * H ^ 18 + (116095057920 : K[X]) * a2 * a3 ^ 2 * a5 * H ^ 21 +
    (116095057920 : K[X]) * a2 * a3 * a4 ^ 2 * H ^ 21 - (270888468480 :
    K[X]) * a2 * a3 * a4 * a5 ^ 2 * H ^ 18 + (75246796800 : K[X]) * a2 *
    a3 * a5 ^ 4 * H ^ 15 - (90296156160 : K[X]) * a2 * a4 ^ 3 * a5 * H ^
    18 + (150493593600 : K[X]) * a2 * a4 ^ 2 * a5 ^ 3 * H ^ 15 -
    (65213890560 : K[X]) * a2 * a4 * a5 ^ 5 * H ^ 12 + (8281128960 : K[X])
    * a2 * a5 ^ 7 * H ^ 9 + (38698352640 : K[X]) * a3 ^ 3 * a4 * H ^ 21 -
    (45148078080 : K[X]) * a3 ^ 3 * a5 ^ 2 * H ^ 18 - (135444234240 :
    K[X]) * a3 ^ 2 * a4 ^ 2 * a5 * H ^ 18 + (150493593600 : K[X]) * a3 ^ 2
    * a4 * a5 ^ 3 * H ^ 15 - (32606945280 : K[X]) * a3 ^ 2 * a5 ^ 5 * H ^
    12 - (22574039040 : K[X]) * a3 * a4 ^ 4 * H ^ 18 + (150493593600 :
    K[X]) * a3 * a4 ^ 3 * a5 ^ 2 * H ^ 15 - (163034726400 : K[X]) * a3 *
    a4 ^ 2 * a5 ^ 4 * H ^ 12 + (57967902720 : K[X]) * a3 * a4 * a5 ^ 6 * H
    ^ 9 - (6555893760 : K[X]) * a3 * a5 ^ 8 * H ^ 6 + (15049359360 : K[X])
    * a4 ^ 5 * a5 * H ^ 15 - (54344908800 : K[X]) * a4 ^ 4 * a5 ^ 3 * H ^
    12 + (57967902720 : K[X]) * a4 ^ 3 * a5 ^ 5 * H ^ 9 - (26223575040 :
    K[X]) * a4 ^ 2 * a5 ^ 7 * H ^ 6 + (5341839360 : K[X]) * a4 * a5 ^ 9 *
    H ^ 3 - (404684800 : K[X]) * a5 ^ 11 + Polynomial.C κ * ((23219011584
    : K[X]) * a0 * a3 * H ^ 26 - (15479341056 : K[X]) * a0 * a4 * a5 * H ^
    23 + (4299816960 : K[X]) * a0 * a5 ^ 3 * H ^ 20 + (23219011584 : K[X])
    * a1 * a2 * H ^ 26 - (15479341056 : K[X]) * a1 * a3 * a5 * H ^ 23 -
    (7739670528 : K[X]) * a1 * a4 ^ 2 * H ^ 23 + (12899450880 : K[X]) * a1
    * a4 * a5 ^ 2 * H ^ 20 - (2866544640 : K[X]) * a1 * a5 ^ 4 * H ^ 17 -
    (7739670528 : K[X]) * a2 ^ 2 * a5 * H ^ 23 - (15479341056 : K[X]) * a2
    * a3 * a4 * H ^ 23 + (12899450880 : K[X]) * a2 * a3 * a5 ^ 2 * H ^ 20
    + (12899450880 : K[X]) * a2 * a4 ^ 2 * a5 * H ^ 20 - (11466178560 :
    K[X]) * a2 * a4 * a5 ^ 3 * H ^ 17 + (2102132736 : K[X]) * a2 * a5 ^ 5
    * H ^ 14 - (2579890176 : K[X]) * a3 ^ 3 * H ^ 23 + (12899450880 :
    K[X]) * a3 ^ 2 * a4 * a5 * H ^ 20 - (5733089280 : K[X]) * a3 ^ 2 * a5
    ^ 3 * H ^ 17 + (4299816960 : K[X]) * a3 * a4 ^ 3 * H ^ 20 -
    (17199267840 : K[X]) * a3 * a4 ^ 2 * a5 ^ 2 * H ^ 17 + (10510663680 :
    K[X]) * a3 * a4 * a5 ^ 4 * H ^ 14 - (1634992128 : K[X]) * a3 * a5 ^ 6
    * H ^ 11 - (2866544640 : K[X]) * a4 ^ 4 * a5 * H ^ 17 + (7007109120 :
    K[X]) * a4 ^ 3 * a5 ^ 3 * H ^ 14 - (4904976384 : K[X]) * a4 ^ 2 * a5 ^
    5 * H ^ 11 + (1323565056 : K[X]) * a4 * a5 ^ 7 * H ^ 8 - (122552320 :
    K[X]) * a5 ^ 9 * H ^ 5)) - ((1128701952 : K[X]) * a0 * a4 * H ^ 18 -
    (470292480 : K[X]) * a0 * a5 ^ 2 * H ^ 15 + (1128701952 : K[X]) * a1 *
    a3 * H ^ 18 - (940584960 : K[X]) * a1 * a4 * a5 * H ^ 15 + (287400960
    : K[X]) * a1 * a5 ^ 3 * H ^ 12 + (564350976 : K[X]) * a2 ^ 2 * H ^ 18
    - (940584960 : K[X]) * a2 * a3 * a5 * H ^ 15 - (470292480 : K[X]) * a2
    * a4 ^ 2 * H ^ 15 + (862202880 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 12 -
    (203575680 : K[X]) * a2 * a5 ^ 4 * H ^ 9 - (470292480 : K[X]) * a3 ^ 2
    * a4 * H ^ 15 + (431101440 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 12 +
    (862202880 : K[X]) * a3 * a4 ^ 2 * a5 * H ^ 12 - (814302720 : K[X]) *
    a3 * a4 * a5 ^ 3 * H ^ 9 + (156074688 : K[X]) * a3 * a5 ^ 5 * H ^ 6 +
    (71850240 : K[X]) * a4 ^ 4 * H ^ 12 - (407151360 : K[X]) * a4 ^ 3 * a5
    ^ 2 * H ^ 9 + (390186720 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 6 -
    (125726832 : K[X]) * a4 * a5 ^ 6 * H ^ 3 + (13096545 : K[X]) * a5 ^ 8)
    * alignedThirdDefect610 H a3 a4 a5 b7 κ - ((67184640 : K[X]) * a0 * H
    ^ 15 - (11197440 : K[X]) * a1 * a5 * H ^ 12 - (11197440 : K[X]) * a2 *
    a4 * H ^ 12 + (6531840 : K[X]) * a2 * a5 ^ 2 * H ^ 9 - (5598720 :
    K[X]) * a3 ^ 2 * H ^ 12 + (13063680 : K[X]) * a3 * a4 * a5 * H ^ 9 -
    (4717440 : K[X]) * a3 * a5 ^ 3 * H ^ 6 + (2177280 : K[X]) * a4 ^ 3 * H
    ^ 9 - (7076160 : K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 6 + (3734640 : K[X]) *
    a4 * a5 ^ 4 * H ^ 3 - (518700 : K[X]) * a5 ^ 6) *
    alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ - ((2985984 : K[X])
    * a1 * H ^ 12 - (995328 : K[X]) * a2 * a5 * H ^ 9 - (995328 : K[X]) *
    a3 * a4 * H ^ 9 + (663552 : K[X]) * a3 * a5 ^ 2 * H ^ 6 + (663552 :
    K[X]) * a4 ^ 2 * a5 * H ^ 6 - (516096 : K[X]) * a4 * a5 ^ 3 * H ^ 3 +
    (86016 : K[X]) * a5 ^ 5) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5
    b4 b5 b6 b7 κ - ((93312 : K[X]) * a2 * H ^ 9 - (46656 : K[X]) * a3 *
    a5 * H ^ 6 - (23328 : K[X]) * a4 ^ 2 * H ^ 6 + (34992 : K[X]) * a4 *
    a5 ^ 2 * H ^ 3 - (7290 : K[X]) * a5 ^ 4) * alignedSeventhDefect610 H
    a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - ((10368 : K[X]) * a3 * H ^ 6 -
    (6912 : K[X]) * a4 * a5 * H ^ 3 + (1920 : K[X]) * a5 ^ 3) *
    alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ - ((48
    : K[X]) * a4 * H ^ 3 - (20 : K[X]) * a5 ^ 2) * alignedNinthDefect610 H
    a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Scalar resolution of the eleventh-row peeled head at the root
against `e₂(a) = 0`, the `u₂` root product, and the carried tenth-face
tie `135 s = 92160 x² (81 p - y)²`: the head equation forces the exact
vanishing `t = 0` of the new μ-loaded witness. -/
theorem alignedEleventhSquareTieResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v y p s t m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : v = 0)
    (htie : 135 * s = 92160 * x ^ 2 * (81 * p - y) ^ 2)
    (hhead : -61931520 * u ^ 4 * x ^ 3 + 1433272320 * u ^ 2 * p * x ^ 3 -
      22118400 * u ^ 2 * y * x ^ 3 + 655360 * u * v ^ 3 - 21168 * u * m *
      x ^ 6 - 9674588160 * p ^ 2 * x ^ 3 + 238878720 * p * y * x ^ 3 +
      2160 * s * x + 1215 * t - 1474560 * y ^ 2 * x ^ 3 = 0) :
    t = 0 := by
  have hux2 : u * x ^ 2 = 0 := by
    linear_combination (-(3 : K)⁻¹) * h1 + ((3 : K)⁻¹ * x) * h2
  have hux : u * x = 0 := by
    rcases mul_eq_zero.mp hux2 with hu | hx2
    · rw [hu, zero_mul]
    · rw [(pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx2, mul_zero]
  linear_combination ((1215 : K)⁻¹) * hhead -
    ((1215 : K)⁻¹ * 16 * x) * htie +
    ((1215 : K)⁻¹ * (21168 * m * x ^ 5 - 1433272320 * p * u * x ^ 2 +
      61931520 * u ^ 3 * x ^ 2 + 22118400 * u * x ^ 2 * y)) * hux -
    ((1215 : K)⁻¹ * 655360 * u * v ^ 2) * h2

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 1600000000 in
/-- Peeled square-chamber form of the consumed degree-`4` row
(`h₀⁴⁴ · h₀² · h₀ · h₀` cancelled along the seventh-face
divisibilities, the eighth-face product divisor `u₂`, the tenth-face
μ-loaded divisor `s₂`, and the NEW divisor `s₄`): the FIRST aligned
square-chamber row with no `q`-coefficient at all.  On the face it
equals `μ₄ h₀⁷`. -/
def alignedEleventhSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 u2 s2 s4 a0 a1 a2 : K[X])
    (κ μ ν κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  (-((61931520 : K[X]) * e1 ^ 4 * w1 ^ 3) - (22118400 : K[X]) * e1 ^ 2 *
    u2 * w1 ^ 3 + (1433272320 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360 :
    K[X]) * e1 * e2 ^ 3 - (1474560 : K[X]) * u2 ^ 2 * w1 ^ 3 + (238878720
    : K[X]) * u2 * w1 ^ 3 * a2 + (2160 : K[X]) * s2 * w1 + (1215 : K[X]) *
    s4 - (9674588160 : K[X]) * w1 ^ 3 * a2 ^ 2 - Polynomial.C μ * ((21168
    : K[X]) * e1 * w1 ^ 6)) + h0 * ((61931520 : K[X]) * e1 ^ 5 * w1 -
    (10321920 : K[X]) * e1 ^ 4 * e2 + (103219200 : K[X]) * e1 ^ 3 * u2 *
    w1 - (3344302080 : K[X]) * e1 ^ 3 * w1 * a2 - (20643840 : K[X]) * e1 ^
    2 * e2 * u2 + (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (19660800 :
    K[X]) * e1 * u2 ^ 2 * w1 - (1911029760 : K[X]) * e1 * u2 * w1 * a2 +
    (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 - (1638400 : K[X]) * e2 * u2 ^
    2 + (159252480 : K[X]) * e2 * u2 * a2 - (3224862720 : K[X]) * e2 * a2
    ^ 2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
    ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) - Polynomial.C μ * ((28224 : K[X])
    * u2 * w1 ^ 4) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 * a2) +
    Polynomial.C κ * ((17694720 : K[X]) * e1 ^ 3 * w1 ^ 3) + Polynomial.C
    κ * ((3538944 : K[X]) * e1 * u2 * w1 ^ 3) - Polynomial.C κ *
    ((286654464 : K[X]) * e1 * w1 ^ 3 * a2) - Polynomial.C κ * ((131072 :
    K[X]) * e2 ^ 3)) + h0 ^ 2 * (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 *
    a1) - (119439360 : K[X]) * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1
    ^ 2 * a1 + (58047528960 : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν *
    ((10800 : K[X]) * e1 * w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) *
    e1 ^ 3 * w1 ^ 2) + Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) +
    Polynomial.C μ * ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C
    μ * ((78382080 : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ *
    ((35389440 : K[X]) * e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X])
    * e1 ^ 3 * e2) - Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 *
    w1) + Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
    Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ *
    ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
    K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 * w1
    * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) + h0 ^ 3
    * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) * e1 * u2 *
    a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂ * ((54 :
    K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2 * w1 ^ 2)
    + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C ν * ((28800
    : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 : K[X]) * w1 ^ 2 *
    a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) - Polynomial.C μ *
    ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ * ((52254720 : K[X])
    * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 : K[X]) * u2 ^ 2) +
    Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) - Polynomial.C μ *
    ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ * ((564350976 :
    K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 : K[X]) * e1 * w1 ^ 2 *
    a1)) + h0 ^ 4 * ((12899450880 : K[X]) * e1 ^ 2 * w1 * a0 - (2149908480
    : K[X]) * e1 * e2 * a0 + (2149908480 : K[X]) * u2 * w1 * a0 -
    (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440 : K[X]) * w1 * a1
    ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^ 2) - Polynomial.C
    κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C κ₅ * ((12288 :
    K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X]) * u2 * w1) +
    Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) - Polynomial.C ν *
    ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν * ((161280 : K[X]) * e1 *
    u2) + Polynomial.C ν * ((3732480 : K[X]) * e1 * a2) + Polynomial.C μ *
    ((313528320 : K[X]) * e1 * w1 * a1) - Polynomial.C μ * ((41803776 :
    K[X]) * e2 * a1) - Polynomial.C κ * ((859963392 : K[X]) * e1 ^ 2 * a1)
    - Polynomial.C κ * ((573308928 : K[X]) * u2 * a1) + Polynomial.C κ *
    ((23219011584 : K[X]) * a1 * a2)) + h0 ^ 5 * (Polynomial.C μ₃ * ((4 :
    K[X]) * w1 ^ 2) + Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) -
    Polynomial.C κ₇ * ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 :
    K[X]) * e1 ^ 2) + Polynomial.C ν₂ * ((1728 : K[X]) * u2) -
    Polynomial.C ν₂ * ((93312 : K[X]) * a2) + Polynomial.C ν * ((11197440
    : K[X]) * w1 * a1) + Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 *
    a0) - Polynomial.C κ * ((5159780352 : K[X]) * e1 * w1 * a0) +
    Polynomial.C κ * ((859963392 : K[X]) * e2 * a0)) + h0 ^ 6 *
    ((522427760640 : K[X]) * a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) *
    e1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C μ *
    ((376233984 : K[X]) * e1 * a0)) + h0 ^ 7 * (-(Polynomial.C ν *
    ((67184640 : K[X]) * a0)))

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Residue of the vanished nonsquare eleventh defect after the
carried divisor cascade (`t₁, t₂`, then the `p₂` divisor `u` squared,
then the `t₃` divisor cubed, then the `v` divisor squared) peels
`H²⁸`: an inhomogeneous relation on the carried witnesses only — no
new witness and no `q`-coefficient.  On the face it vanishes, and its
root evaluation is the first `p₀`-loaded root relation of the aligned
nonsquare tower. -/
def alignedEleventhNonsquareResidue610 {K : Type*} [CommRing K]
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₅ κ₇ : K) : K[X] :=
  ((80640 : K[X]) * t1 ^ 4 * t3 - (46080 : K[X]) * t1 ^ 3 * v - (46080 :
    K[X]) * t1 ^ 2 * u * t3 + (23040 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1 +
    (23040 : K[X]) * t1 * u * v - (23040 : K[X]) * t1 * t3 * v * g1 +
    (16796160 : K[X]) * t1 * t3 * a0 + (3840 : K[X]) * u ^ 2 * t3 - (3840
    : K[X]) * u * t3 ^ 2 * g1 + (1280 : K[X]) * t3 ^ 3 * g1 ^ 2 + (11520 :
    K[X]) * v ^ 2 * g1 - (16796160 : K[X]) * v * a0 + Polynomial.C κ₇ *
    ((3 : K[X]) * t3) - Polynomial.C κ₅ * ((96 : K[X]) * t1 * t3) +
    Polynomial.C κ₅ * ((96 : K[X]) * v) - Polynomial.C κ * ((46080 : K[X])
    * t1 ^ 3 * t3) + Polynomial.C κ * ((27648 : K[X]) * t1 ^ 2 * v) +
    Polynomial.C κ * ((18432 : K[X]) * t1 * u * t3) - Polynomial.C κ *
    ((9216 : K[X]) * t1 * t3 ^ 2 * g1) - Polynomial.C κ * ((9216 : K[X]) *
    u * v) + Polynomial.C κ * ((9216 : K[X]) * t3 * v * g1) - Polynomial.C
    κ * ((6718464 : K[X]) * t3 * a0)) + H * (-((5120 : K[X]) * t1 * t3 ^
    3) + (3840 : K[X]) * t3 ^ 2 * v + Polynomial.C κ * ((1024 : K[X]) * t3
    ^ 3))

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- In the square chamber the squared weight-`55/2` integral has a
polynomial square root: `Λ = μ₄ h₀⁵⁵` with `μ₄² = κ₁₀`.  The constant
`μ₄` is preserved, not cleared. -/
theorem alignedSquareEleventh_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₁₀ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hL2 :
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 55) :
    ∃ μ₄ : K, μ₄ ^ 2 = κ₁₀ ∧
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ =
        Polynomial.C μ₄ * h0 ^ 55 := by
  set L : K[X] :=
    alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (h0 ^ 55) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₁₀, ?_⟩
    rw [hL2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ := by
    have h110 := hL2
    rw [hG, hHsq] at h110
    apply mul_left_cancel₀ (pow_ne_zero 110 hh0)
    linear_combination h110
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₁₀
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₄, hμ⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨μ₄, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₄ ^ 2) = Polynomial.C κ₁₀ := by
      rw [Polynomial.C_pow, hμ, hG2]
    exact Polynomial.C_injective hCμ
  · rw [hG, ← hμ]
    ring

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- In the nonsquare chamber the odd exponent forces both the constant
and the eleventh defect to vanish: `κ₁₀ = 0` and `Λ ≡ 0`, exactly as
for `D`, `F`, `I`, and `L`. -/
theorem alignedNonsquareEleventh_defect_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₁₀ : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hL2 :
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 55) :
    κ₁₀ = 0 ∧
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
        κ = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set L : K[X] :=
    alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (H ^ 27) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₁₀ * H, ?_⟩
    rw [hL2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 54 hH)
    have h54 := hL2
    rw [hG] at h54
    linear_combination h54
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₁₀ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk10 : κ₁₀ = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hLzero : L = 0 := by
    have hsq : L ^ 2 = 0 := by
      rw [hL2, hk10]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk10, hLzero⟩

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`4` row in the nonsquare chamber:
the eleventh defect vanishes identically, the `H²²`-peeled core
absorbs the undecic head through the seventh-face divisibilities,
peeling `H²` onto the squared carried `p₂` divisor, one `H` onto the
cubed carried `t₃` divisor, one `H` onto the squared carried `v`
divisor, and `H²` beyond — bottoming out on the residue relation
WITHOUT any new witness: every divisor of the cascade is carried. -/
theorem alignedNonsquareEleventh_descent_610 {K : Type*}
    [Field K] [CharZero K]
    {H g1 f t1 t2 u t3 v a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 :
      K[X]}
    {κ κ₅ κ₇ : K}
    (hH : H ≠ 0)
    (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI0 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ = 0)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL0 : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = 0)
    (hLam0 : alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4
        b5 b6 b7 κ = 0)
    (ht1 : (3 : K[X]) * f - g1 ^ 2 = H * t1)
    (ht2 : (27 : K[X]) * a3 - g1 ^ 3 = H * t2)
    (hu : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
      H * u)
    (ht3 : t2 - (6 : K[X]) * g1 * t1 = H * t3)
    (hv : (243 : K[X]) * a1 - g1 * u = H * v) :
    alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇ =
      0 := by
  have hL' := hLam0
  unfold alignedEleventhDefect610 at hL'
  rw [hD0, hF0, hG, hI0, hJ, hL0, hg1, hf] at hL'
  have hcore :
      ((15049359360 : K[X]) * f ^ 5 * g1 - (22574039040 : K[X]) * f ^ 4 *
      a3 - (54344908800 : K[X]) * f ^ 4 * g1 ^ 3 + (150493593600 : K[X]) *
      f ^ 3 * a3 * g1 ^ 2 + (57967902720 : K[X]) * f ^ 3 * g1 ^ 5 -
      (135444234240 : K[X]) * f ^ 2 * a3 ^ 2 * g1 - (163034726400 : K[X])
      * f ^ 2 * a3 * g1 ^ 4 - (26223575040 : K[X]) * f ^ 2 * g1 ^ 7 +
      (38698352640 : K[X]) * f * a3 ^ 3 + (150493593600 : K[X]) * f * a3 ^
      2 * g1 ^ 3 + (57967902720 : K[X]) * f * a3 * g1 ^ 6 + (5341839360 :
      K[X]) * f * g1 ^ 9 - (45148078080 : K[X]) * a3 ^ 3 * g1 ^ 2 -
      (32606945280 : K[X]) * a3 ^ 2 * g1 ^ 5 - (6555893760 : K[X]) * a3 *
      g1 ^ 8 - (404684800 : K[X]) * g1 ^ 11) + H * (-((90296156160 : K[X])
      * f ^ 3 * g1 * a2) + (116095057920 : K[X]) * f ^ 2 * a3 * a2 +
      (150493593600 : K[X]) * f ^ 2 * g1 ^ 3 * a2 - (270888468480 : K[X])
      * f * a3 * g1 ^ 2 * a2 - (65213890560 : K[X]) * f * g1 ^ 5 * a2 +
      (116095057920 : K[X]) * a3 ^ 2 * g1 * a2 + (75246796800 : K[X]) * a3
      * g1 ^ 4 * a2 + (8281128960 : K[X]) * g1 ^ 7 * a2 - Polynomial.C κ *
      ((2866544640 : K[X]) * f ^ 4 * g1) + Polynomial.C κ * ((4299816960 :
      K[X]) * f ^ 3 * a3) + Polynomial.C κ * ((7007109120 : K[X]) * f ^ 3
      * g1 ^ 3) - Polynomial.C κ * ((17199267840 : K[X]) * f ^ 2 * a3 * g1
      ^ 2) - Polynomial.C κ * ((4904976384 : K[X]) * f ^ 2 * g1 ^ 5) +
      Polynomial.C κ * ((12899450880 : K[X]) * f * a3 ^ 2 * g1) +
      Polynomial.C κ * ((10510663680 : K[X]) * f * a3 * g1 ^ 4) +
      Polynomial.C κ * ((1323565056 : K[X]) * f * g1 ^ 7) - Polynomial.C κ
      * ((2579890176 : K[X]) * a3 ^ 3) - Polynomial.C κ * ((5733089280 :
      K[X]) * a3 ^ 2 * g1 ^ 3) - Polynomial.C κ * ((1634992128 : K[X]) *
      a3 * g1 ^ 6) - Polynomial.C κ * ((122552320 : K[X]) * g1 ^ 9)) + H ^
      2 * ((38698352640 : K[X]) * f ^ 3 * a1 - (135444234240 : K[X]) * f ^
      2 * g1 ^ 2 * a1 + (232190115840 : K[X]) * f * a3 * g1 * a1 +
      (75246796800 : K[X]) * f * g1 ^ 4 * a1 + (116095057920 : K[X]) * f *
      g1 * a2 ^ 2 - (87071293440 : K[X]) * a3 ^ 2 * a1 - (90296156160 :
      K[X]) * a3 * g1 ^ 3 * a1 - (87071293440 : K[X]) * a3 * a2 ^ 2 -
      (10868981760 : K[X]) * g1 ^ 6 * a1 - (45148078080 : K[X]) * g1 ^ 3 *
      a2 ^ 2 + Polynomial.C κ * ((12899450880 : K[X]) * f ^ 2 * g1 * a2) -
      Polynomial.C κ * ((15479341056 : K[X]) * f * a3 * a2) - Polynomial.C
      κ * ((11466178560 : K[X]) * f * g1 ^ 3 * a2) + Polynomial.C κ *
      ((12899450880 : K[X]) * a3 * g1 ^ 2 * a2) + Polynomial.C κ *
      ((2102132736 : K[X]) * g1 ^ 5 * a2)) + H ^ 3 * ((116095057920 :
      K[X]) * f ^ 2 * g1 * a0 - (174142586880 : K[X]) * f * a3 * a0 -
      (90296156160 : K[X]) * f * g1 ^ 3 * a0 - (174142586880 : K[X]) * f *
      a1 * a2 + (116095057920 : K[X]) * a3 * g1 ^ 2 * a0 + (15049359360 :
      K[X]) * g1 ^ 5 * a0 + (116095057920 : K[X]) * g1 ^ 2 * a1 * a2 -
      Polynomial.C κ₅ * ((663552 : K[X]) * f ^ 2 * g1) + Polynomial.C κ₅ *
      ((995328 : K[X]) * f * a3) + Polynomial.C κ₅ * ((516096 : K[X]) * f
      * g1 ^ 3) - Polynomial.C κ₅ * ((663552 : K[X]) * a3 * g1 ^ 2) -
      Polynomial.C κ₅ * ((86016 : K[X]) * g1 ^ 5) - Polynomial.C κ *
      ((7739670528 : K[X]) * f ^ 2 * a1) + Polynomial.C κ * ((12899450880
      : K[X]) * f * g1 ^ 2 * a1) - Polynomial.C κ * ((15479341056 : K[X])
      * a3 * g1 * a1) - Polynomial.C κ * ((2866544640 : K[X]) * g1 ^ 4 *
      a1) - Polynomial.C κ * ((7739670528 : K[X]) * g1 * a2 ^ 2)) + H ^ 4
      * (-((174142586880 : K[X]) * g1 * a0 * a2) - (87071293440 : K[X]) *
      g1 * a1 ^ 2 + Polynomial.C κ₇ * ((6912 : K[X]) * f * g1) -
      Polynomial.C κ₇ * ((10368 : K[X]) * a3) - Polynomial.C κ₇ * ((1920 :
      K[X]) * g1 ^ 3) + Polynomial.C κ₅ * ((995328 : K[X]) * g1 * a2) -
      Polynomial.C κ * ((15479341056 : K[X]) * f * g1 * a0) + Polynomial.C
      κ * ((23219011584 : K[X]) * a3 * a0) + Polynomial.C κ * ((4299816960
      : K[X]) * g1 ^ 3 * a0) + Polynomial.C κ * ((23219011584 : K[X]) * a1
      * a2)) + H ^ 5 * ((522427760640 : K[X]) * a0 * a1 - Polynomial.C κ₅
      * ((2985984 : K[X]) * a1)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 22 hH)
    linear_combination hL'
  have hR2n :
      (-((13271040 : K[X]) * t1 ^ 2 * g1 ^ 7) + (8847360 : K[X]) * t1 * t2
      * g1 ^ 6 - (716636160 : K[X]) * t1 * g1 ^ 5 * a2 - (1474560 : K[X])
      * t2 ^ 2 * g1 ^ 5 + (238878720 : K[X]) * t2 * g1 ^ 4 * a2 -
      (9674588160 : K[X]) * g1 ^ 3 * a2 ^ 2) + H * ((247726080 : K[X]) *
      t1 ^ 3 * g1 ^ 5 - (154828800 : K[X]) * t1 ^ 2 * t2 * g1 ^ 4 +
      (7166361600 : K[X]) * t1 ^ 2 * g1 ^ 3 * a2 + (29491200 : K[X]) * t1
      * t2 ^ 2 * g1 ^ 3 - (2388787200 : K[X]) * t1 * t2 * g1 ^ 2 * a2 +
      (2149908480 : K[X]) * t1 * g1 ^ 4 * a1 + (38698352640 : K[X]) * t1 *
      g1 * a2 ^ 2 - (1638400 : K[X]) * t2 ^ 3 * g1 ^ 2 + (159252480 :
      K[X]) * t2 ^ 2 * g1 * a2 - (716636160 : K[X]) * t2 * g1 ^ 3 * a1 -
      (3224862720 : K[X]) * t2 * a2 ^ 2 + (58047528960 : K[X]) * g1 ^ 2 *
      a1 * a2 - Polynomial.C κ * ((31850496 : K[X]) * t1 ^ 2 * g1 ^ 5) +
      Polynomial.C κ * ((17694720 : K[X]) * t1 * t2 * g1 ^ 4) -
      Polynomial.C κ * ((1146617856 : K[X]) * t1 * g1 ^ 3 * a2) -
      Polynomial.C κ * ((2359296 : K[X]) * t2 ^ 2 * g1 ^ 3) + Polynomial.C
      κ * ((286654464 : K[X]) * t2 * g1 ^ 2 * a2) - Polynomial.C κ *
      ((7739670528 : K[X]) * g1 * a2 ^ 2)) + H ^ 2 * (-((371589120 : K[X])
      * t1 ^ 4 * g1 ^ 3) + (165150720 : K[X]) * t1 ^ 3 * t2 * g1 ^ 2 -
      (3344302080 : K[X]) * t1 ^ 3 * g1 * a2 - (20643840 : K[X]) * t1 ^ 2
      * t2 ^ 2 * g1 + (477757440 : K[X]) * t1 ^ 2 * t2 * a2 - (10749542400
      : K[X]) * t1 ^ 2 * g1 ^ 2 * a1 + (655360 : K[X]) * t1 * t2 ^ 3 +
      (2866544640 : K[X]) * t1 * t2 * g1 * a1 - (6449725440 : K[X]) * t1 *
      g1 ^ 3 * a0 - (58047528960 : K[X]) * t1 * a1 * a2 - (119439360 :
      K[X]) * t2 ^ 2 * a1 + (2149908480 : K[X]) * t2 * g1 ^ 2 * a0 -
      (174142586880 : K[X]) * g1 * a0 * a2 - (87071293440 : K[X]) * g1 *
      a1 ^ 2 + Polynomial.C κ₅ * ((36864 : K[X]) * t1 * g1 ^ 3) -
      Polynomial.C κ₅ * ((12288 : K[X]) * t2 * g1 ^ 2) + Polynomial.C κ₅ *
      ((995328 : K[X]) * g1 * a2) + Polynomial.C κ * ((123863040 : K[X]) *
      t1 ^ 3 * g1 ^ 3) - Polynomial.C κ * ((53084160 : K[X]) * t1 ^ 2 * t2
      * g1 ^ 2) + Polynomial.C κ * ((1433272320 : K[X]) * t1 ^ 2 * g1 *
      a2) + Polynomial.C κ * ((5898240 : K[X]) * t1 * t2 ^ 2 * g1) -
      Polynomial.C κ * ((191102976 : K[X]) * t1 * t2 * a2) + Polynomial.C
      κ * ((2579890176 : K[X]) * t1 * g1 ^ 2 * a1) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 3) - Polynomial.C κ * ((573308928 : K[X]) *
      t2 * g1 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 * a2)) +
      H ^ 3 * ((61931520 : K[X]) * t1 ^ 5 * g1 - (10321920 : K[X]) * t1 ^
      4 * t2 + (1433272320 : K[X]) * t1 ^ 3 * a1 + (12899450880 : K[X]) *
      t1 ^ 2 * g1 * a0 - (2149908480 : K[X]) * t1 * t2 * a0 +
      (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₇ * ((2304 : K[X]) *
      t1 * g1) - Polynomial.C κ₇ * ((384 : K[X]) * t2) - Polynomial.C κ₅ *
      ((73728 : K[X]) * t1 ^ 2 * g1) + Polynomial.C κ₅ * ((12288 : K[X]) *
      t1 * t2) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C
      κ * ((35389440 : K[X]) * t1 ^ 4 * g1) + Polynomial.C κ * ((5898240 :
      K[X]) * t1 ^ 3 * t2) - Polynomial.C κ * ((859963392 : K[X]) * t1 ^ 2
      * a1) - Polynomial.C κ * ((5159780352 : K[X]) * t1 * g1 * a0) +
      Polynomial.C κ * ((859963392 : K[X]) * t2 * a0)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination hcore + (-((61931520 : K[X]) * t1 ^ 4 * g1 * H ^ 4 - (423198720 : K[X]) * t1 ^
      3 * g1 ^ 3 * H ^ 3 + (185794560 : K[X]) * t1 ^ 3 * g1 * f * H ^ 3 -
      (278691840 : K[X]) * t1 ^ 3 * a3 * H ^ 3 + (505774080 : K[X]) * t1 ^
      2 * g1 ^ 5 * H ^ 2 - (1455390720 : K[X]) * t1 ^ 2 * g1 ^ 3 * f * H ^
      2 + (4737761280 : K[X]) * t1 ^ 2 * g1 ^ 2 * a3 * H ^ 2 + (557383680
      : K[X]) * t1 ^ 2 * g1 * f ^ 2 * H ^ 2 - (3344302080 : K[X]) * t1 ^ 2
      * g1 * a2 * H ^ 3 - (836075520 : K[X]) * t1 ^ 2 * f * a3 * H ^ 2 +
      (1433272320 : K[X]) * t1 ^ 2 * a1 * H ^ 4 - (384860160 : K[X]) * t1
      * g1 ^ 7 * H + (2972712960 : K[X]) * t1 * g1 ^ 5 * f * H -
      (7803371520 : K[X]) * t1 * g1 ^ 4 * a3 * H - (4923555840 : K[X]) *
      t1 * g1 ^ 3 * f ^ 2 * H + (10032906240 : K[X]) * t1 * g1 ^ 3 * a2 *
      H ^ 2 + (15049359360 : K[X]) * t1 * g1 ^ 2 * f * a3 * H -
      (12182814720 : K[X]) * t1 * g1 ^ 2 * a1 * H ^ 3 + (1672151040 :
      K[X]) * t1 * g1 * f ^ 3 * H - (10032906240 : K[X]) * t1 * g1 * f *
      a2 * H ^ 2 - (15049359360 : K[X]) * t1 * g1 * a3 ^ 2 * H +
      (12899450880 : K[X]) * t1 * g1 * a0 * H ^ 4 - (2508226560 : K[X]) *
      t1 * f ^ 2 * a3 * H + (4299816960 : K[X]) * t1 * f * a1 * H ^ 3 +
      (12899450880 : K[X]) * t1 * a3 * a2 * H ^ 2 + (404848640 : K[X]) *
      g1 ^ 9 - (4127293440 : K[X]) * g1 ^ 7 * f + (6502809600 : K[X]) * g1
      ^ 6 * a3 + (13841694720 : K[X]) * g1 ^ 5 * f ^ 2 - (8360755200 :
      K[X]) * g1 ^ 5 * a2 * H - (38459473920 : K[X]) * g1 ^ 4 * f * a3 +
      (11466178560 : K[X]) * g1 ^ 4 * a1 * H ^ 2 - (16442818560 : K[X]) *
      g1 ^ 3 * f ^ 3 + (40131624960 : K[X]) * g1 ^ 3 * f * a2 * H +
      (35115171840 : K[X]) * g1 ^ 3 * a3 ^ 2 - (17199267840 : K[X]) * g1 ^
      3 * a0 * H ^ 3 + (47656304640 : K[X]) * g1 ^ 2 * f ^ 2 * a3 -
      (40848261120 : K[X]) * g1 ^ 2 * f * a1 * H ^ 2 - (77396705280 :
      K[X]) * g1 ^ 2 * a3 * a2 * H + (5016453120 : K[X]) * g1 * f ^ 4 -
      (30098718720 : K[X]) * g1 * f ^ 2 * a2 * H - (45148078080 : K[X]) *
      g1 * f * a3 ^ 2 + (38698352640 : K[X]) * g1 * f * a0 * H ^ 3 +
      (77396705280 : K[X]) * g1 * a3 * a1 * H ^ 2 + (38698352640 : K[X]) *
      g1 * a2 ^ 2 * H ^ 2 - (7524679680 : K[X]) * f ^ 3 * a3 +
      (12899450880 : K[X]) * f ^ 2 * a1 * H ^ 2 + (38698352640 : K[X]) * f
      * a3 * a2 * H + (12899450880 : K[X]) * a3 ^ 3 - (58047528960 : K[X])
      * a3 * a0 * H ^ 3 - (58047528960 : K[X]) * a1 * a2 * H ^ 3 +
      Polynomial.C κ₇ * ((2304 : K[X]) * g1 * H ^ 4) - Polynomial.C κ₅ *
      ((73728 : K[X]) * t1 * g1 * H ^ 4) + Polynomial.C κ₅ * ((98304 :
      K[X]) * g1 ^ 3 * H ^ 3) - Polynomial.C κ₅ * ((221184 : K[X]) * g1 *
      f * H ^ 3) + Polynomial.C κ₅ * ((331776 : K[X]) * a3 * H ^ 3) -
      Polynomial.C κ * ((35389440 : K[X]) * t1 ^ 3 * g1 * H ^ 4) +
      Polynomial.C κ * ((153354240 : K[X]) * t1 ^ 2 * g1 ^ 3 * H ^ 3) -
      Polynomial.C κ * ((106168320 : K[X]) * t1 ^ 2 * g1 * f * H ^ 3) +
      Polynomial.C κ * ((159252480 : K[X]) * t1 ^ 2 * a3 * H ^ 3) -
      Polynomial.C κ * ((132120576 : K[X]) * t1 * g1 ^ 5 * H ^ 2) +
      Polynomial.C κ * ((566231040 : K[X]) * t1 * g1 ^ 3 * f * H ^ 2) -
      Polynomial.C κ * ((1592524800 : K[X]) * t1 * g1 ^ 2 * a3 * H ^ 2) -
      Polynomial.C κ * ((318504960 : K[X]) * t1 * g1 * f ^ 2 * H ^ 2) +
      Polynomial.C κ * ((1433272320 : K[X]) * t1 * g1 * a2 * H ^ 3) +
      Polynomial.C κ * ((477757440 : K[X]) * t1 * f * a3 * H ^ 2) -
      Polynomial.C κ * ((859963392 : K[X]) * t1 * a1 * H ^ 4) +
      Polynomial.C κ * ((120324096 : K[X]) * g1 ^ 7 * H) - Polynomial.C κ
      * ((962592768 : K[X]) * g1 ^ 5 * f * H) + Polynomial.C κ *
      ((1751777280 : K[X]) * g1 ^ 4 * a3 * H) + Polynomial.C κ *
      ((2017198080 : K[X]) * g1 ^ 3 * f ^ 2 * H) - Polynomial.C κ *
      ((2388787200 : K[X]) * g1 ^ 3 * a2 * H ^ 2) - Polynomial.C κ *
      ((5255331840 : K[X]) * g1 ^ 2 * f * a3 * H) + Polynomial.C κ *
      ((3439853568 : K[X]) * g1 ^ 2 * a1 * H ^ 3) - Polynomial.C κ *
      ((955514880 : K[X]) * g1 * f ^ 3 * H) + Polynomial.C κ *
      ((4299816960 : K[X]) * g1 * f * a2 * H ^ 2) + Polynomial.C κ *
      ((4299816960 : K[X]) * g1 * a3 ^ 2 * H) - Polynomial.C κ *
      ((5159780352 : K[X]) * g1 * a0 * H ^ 4) + Polynomial.C κ *
      ((1433272320 : K[X]) * f ^ 2 * a3 * H) - Polynomial.C κ *
      ((2579890176 : K[X]) * f * a1 * H ^ 3) - Polynomial.C κ *
      ((5159780352 : K[X]) * a3 * a2 * H ^ 2))) * ht1 + (-(-((10321920 :
      K[X]) * t1 ^ 4 * H ^ 4) + (165150720 : K[X]) * t1 ^ 3 * g1 ^ 2 * H ^
      3 - (20643840 : K[X]) * t1 ^ 2 * t2 * g1 * H ^ 3 - (134184960 :
      K[X]) * t1 ^ 2 * g1 ^ 4 * H ^ 2 - (557383680 : K[X]) * t1 ^ 2 * g1 *
      a3 * H ^ 2 + (477757440 : K[X]) * t1 ^ 2 * a2 * H ^ 3 + (655360 :
      K[X]) * t1 * t2 ^ 2 * H ^ 3 + (28835840 : K[X]) * t1 * t2 * g1 ^ 3 *
      H ^ 2 + (17694720 : K[X]) * t1 * t2 * a3 * H ^ 2 - (19988480 : K[X])
      * t1 * g1 ^ 6 * H + (760872960 : K[X]) * t1 * g1 ^ 3 * a3 * H -
      (2388787200 : K[X]) * t1 * g1 ^ 2 * a2 * H ^ 2 + (2866544640 : K[X])
      * t1 * g1 * a1 * H ^ 3 + (477757440 : K[X]) * t1 * a3 ^ 2 * H -
      (2149908480 : K[X]) * t1 * a0 * H ^ 4 - (1638400 : K[X]) * t2 ^ 2 *
      g1 ^ 2 * H ^ 2 + (163840 : K[X]) * t2 * g1 ^ 5 * H - (44236800 :
      K[X]) * t2 * g1 ^ 2 * a3 * H + (159252480 : K[X]) * t2 * g1 * a2 * H
      ^ 2 - (119439360 : K[X]) * t2 * a1 * H ^ 3 - (163840 : K[X]) * g1 ^
      8 + (48660480 : K[X]) * g1 ^ 5 * a3 + (79626240 : K[X]) * g1 ^ 4 *
      a2 * H - (597196800 : K[X]) * g1 ^ 3 * a1 * H ^ 2 - (1194393600 :
      K[X]) * g1 ^ 2 * a3 ^ 2 + (2149908480 : K[X]) * g1 ^ 2 * a0 * H ^ 3
      + (4299816960 : K[X]) * g1 * a3 * a2 * H - (3224862720 : K[X]) * a3
      * a1 * H ^ 2 - (3224862720 : K[X]) * a2 ^ 2 * H ^ 2 - Polynomial.C
      κ₇ * ((384 : K[X]) * H ^ 4) + Polynomial.C κ₅ * ((12288 : K[X]) * t1
      * H ^ 4) - Polynomial.C κ₅ * ((12288 : K[X]) * g1 ^ 2 * H ^ 3) +
      Polynomial.C κ * ((5898240 : K[X]) * t1 ^ 3 * H ^ 4) - Polynomial.C
      κ * ((53084160 : K[X]) * t1 ^ 2 * g1 ^ 2 * H ^ 3) + Polynomial.C κ *
      ((5898240 : K[X]) * t1 * t2 * g1 * H ^ 3) + Polynomial.C κ *
      ((11796480 : K[X]) * t1 * g1 ^ 4 * H ^ 2) + Polynomial.C κ *
      ((159252480 : K[X]) * t1 * g1 * a3 * H ^ 2) - Polynomial.C κ *
      ((191102976 : K[X]) * t1 * a2 * H ^ 3) - Polynomial.C κ * ((131072 :
      K[X]) * t2 ^ 2 * H ^ 3) - Polynomial.C κ * ((2228224 : K[X]) * t2 *
      g1 ^ 3 * H ^ 2) - Polynomial.C κ * ((3538944 : K[X]) * t2 * a3 * H ^
      2) + Polynomial.C κ * ((2228224 : K[X]) * g1 ^ 6 * H) - Polynomial.C
      κ * ((56623104 : K[X]) * g1 ^ 3 * a3 * H) + Polynomial.C κ *
      ((286654464 : K[X]) * g1 ^ 2 * a2 * H ^ 2) - Polynomial.C κ *
      ((573308928 : K[X]) * g1 * a1 * H ^ 3) - Polynomial.C κ * ((95551488
      : K[X]) * a3 ^ 2 * H) + Polynomial.C κ * ((859963392 : K[X]) * a0 *
      H ^ 4))) * ht2
  have hR3n :
      ((35389440 : K[X]) * t1 ^ 3 * g1 ^ 5 - (17694720 : K[X]) * t1 ^ 2 *
      t2 * g1 ^ 4 + (2949120 : K[X]) * t1 * t2 ^ 2 * g1 ^ 3 - (163840 :
      K[X]) * t2 ^ 3 * g1 ^ 2) + H * (-((247726080 : K[X]) * t1 ^ 4 * g1 ^
      3) + (106168320 : K[X]) * t1 ^ 3 * t2 * g1 ^ 2 - (14745600 : K[X]) *
      t1 ^ 2 * t2 ^ 2 * g1 + (53084160 : K[X]) * t1 ^ 2 * u * g1 ^ 3 -
      (8599633920 : K[X]) * t1 ^ 2 * g1 ^ 2 * a1 + (655360 : K[X]) * t1 *
      t2 ^ 3 - (14745600 : K[X]) * t1 * t2 * u * g1 ^ 2 + (2149908480 :
      K[X]) * t1 * t2 * g1 * a1 + (983040 : K[X]) * t2 ^ 2 * u * g1 -
      (119439360 : K[X]) * t2 ^ 2 * a1 - (1474560 : K[X]) * u ^ 2 * g1 ^ 3
      + (716636160 : K[X]) * u * g1 ^ 2 * a1 - (87071293440 : K[X]) * g1 *
      a1 ^ 2 + Polynomial.C κ * ((70778880 : K[X]) * t1 ^ 3 * g1 ^ 3) -
      Polynomial.C κ * ((28311552 : K[X]) * t1 ^ 2 * t2 * g1 ^ 2) +
      Polynomial.C κ * ((3538944 : K[X]) * t1 * t2 ^ 2 * g1) -
      Polynomial.C κ * ((7077888 : K[X]) * t1 * u * g1 ^ 3) + Polynomial.C
      κ * ((1719926784 : K[X]) * t1 * g1 ^ 2 * a1) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 3) + Polynomial.C κ * ((1179648 : K[X]) * t2
      * u * g1 ^ 2) - Polynomial.C κ * ((286654464 : K[X]) * t2 * g1 *
      a1)) + H ^ 2 * ((61931520 : K[X]) * t1 ^ 5 * g1 - (10321920 : K[X])
      * t1 ^ 4 * t2 - (41287680 : K[X]) * t1 ^ 3 * u * g1 + (1433272320 :
      K[X]) * t1 ^ 3 * a1 + (5898240 : K[X]) * t1 ^ 2 * t2 * u +
      (12899450880 : K[X]) * t1 ^ 2 * g1 * a0 - (2149908480 : K[X]) * t1 *
      t2 * a0 + (5898240 : K[X]) * t1 * u ^ 2 * g1 - (716636160 : K[X]) *
      t1 * u * a1 - (491520 : K[X]) * t2 * u ^ 2 - (2149908480 : K[X]) * u
      * g1 * a0 + (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₇ *
      ((2304 : K[X]) * t1 * g1) - Polynomial.C κ₇ * ((384 : K[X]) * t2) -
      Polynomial.C κ₅ * ((73728 : K[X]) * t1 ^ 2 * g1) + Polynomial.C κ₅ *
      ((12288 : K[X]) * t1 * t2) + Polynomial.C κ₅ * ((12288 : K[X]) * u *
      g1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C κ *
      ((35389440 : K[X]) * t1 ^ 4 * g1) + Polynomial.C κ * ((5898240 :
      K[X]) * t1 ^ 3 * t2) + Polynomial.C κ * ((17694720 : K[X]) * t1 ^ 2
      * u * g1) - Polynomial.C κ * ((859963392 : K[X]) * t1 ^ 2 * a1) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * t2 * u) - Polynomial.C κ *
      ((5159780352 : K[X]) * t1 * g1 * a0) + Polynomial.C κ * ((859963392
      : K[X]) * t2 * a0) - Polynomial.C κ * ((1179648 : K[X]) * u ^ 2 *
      g1) + Polynomial.C κ * ((286654464 : K[X]) * u * a1)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR2n + (-(-((41287680 : K[X]) * t1 ^ 3 * g1 * H ^ 2) + (5898240 : K[X]) * t1 ^
      2 * t2 * H ^ 2 + (70778880 : K[X]) * t1 ^ 2 * g1 ^ 3 * H - (22118400
      : K[X]) * t1 * t2 * g1 ^ 2 * H + (5898240 : K[X]) * t1 * u * g1 * H
      ^ 2 - (4423680 : K[X]) * t1 * g1 ^ 5 + (477757440 : K[X]) * t1 * g1
      * a2 * H - (716636160 : K[X]) * t1 * a1 * H ^ 2 + (1474560 : K[X]) *
      t2 ^ 2 * g1 * H - (491520 : K[X]) * t2 * u * H ^ 2 + (1474560 :
      K[X]) * t2 * g1 ^ 4 - (39813120 : K[X]) * t2 * a2 * H - (1474560 :
      K[X]) * u * g1 ^ 3 * H - (119439360 : K[X]) * g1 ^ 3 * a2 +
      (716636160 : K[X]) * g1 ^ 2 * a1 * H - (2149908480 : K[X]) * g1 * a0
      * H ^ 2 + Polynomial.C κ₅ * ((12288 : K[X]) * g1 * H ^ 2) +
      Polynomial.C κ * ((17694720 : K[X]) * t1 ^ 2 * g1 * H ^ 2) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * t2 * H ^ 2) - Polynomial.C
      κ * ((10616832 : K[X]) * t1 * g1 ^ 3 * H) + Polynomial.C κ *
      ((2359296 : K[X]) * t2 * g1 ^ 2 * H) - Polynomial.C κ * ((1179648 :
      K[X]) * u * g1 * H ^ 2) - Polynomial.C κ * ((95551488 : K[X]) * g1 *
      a2 * H) + Polynomial.C κ * ((286654464 : K[X]) * a1 * H ^ 2))) * hu
  have hR4n :
      (-((1474560 : K[X]) * u ^ 2 * g1 ^ 3) + (716636160 : K[X]) * u * g1
      ^ 2 * a1 - (87071293440 : K[X]) * g1 * a1 ^ 2) + H * (-((5898240 :
      K[X]) * t1 ^ 3 * u * g1) + (1433272320 : K[X]) * t1 ^ 3 * a1 +
      (2949120 : K[X]) * t1 * u ^ 2 * g1 - (2949120 : K[X]) * t1 * u * t3
      * g1 ^ 2 - (716636160 : K[X]) * t1 * u * a1 + (716636160 : K[X]) *
      t1 * t3 * g1 * a1 - (2149908480 : K[X]) * u * g1 * a0 +
      (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₅ * ((12288 : K[X])
      * u * g1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) + Polynomial.C
      κ * ((3538944 : K[X]) * t1 ^ 2 * u * g1) - Polynomial.C κ *
      ((859963392 : K[X]) * t1 ^ 2 * a1) - Polynomial.C κ * ((1179648 :
      K[X]) * u ^ 2 * g1) + Polynomial.C κ * ((1179648 : K[X]) * u * t3 *
      g1 ^ 2) + Polynomial.C κ * ((286654464 : K[X]) * u * a1) -
      Polynomial.C κ * ((286654464 : K[X]) * t3 * g1 * a1)) + H ^ 2 *
      (-((10321920 : K[X]) * t1 ^ 4 * t3) + (5898240 : K[X]) * t1 ^ 2 * u
      * t3 - (2949120 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1 - (2149908480 : K[X])
      * t1 * t3 * a0 - (491520 : K[X]) * u ^ 2 * t3 + (983040 : K[X]) * u
      * t3 ^ 2 * g1 - (163840 : K[X]) * t3 ^ 3 * g1 ^ 2 - (119439360 :
      K[X]) * t3 ^ 2 * a1 - Polynomial.C κ₇ * ((384 : K[X]) * t3) +
      Polynomial.C κ₅ * ((12288 : K[X]) * t1 * t3) + Polynomial.C κ *
      ((5898240 : K[X]) * t1 ^ 3 * t3) - Polynomial.C κ * ((2359296 :
      K[X]) * t1 * u * t3) + Polynomial.C κ * ((1179648 : K[X]) * t1 * t3
      ^ 2 * g1) + Polynomial.C κ * ((859963392 : K[X]) * t3 * a0)) + H ^ 3
      * ((655360 : K[X]) * t1 * t3 ^ 3 - Polynomial.C κ * ((131072 : K[X])
      * t3 ^ 3)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR3n + (-(-((10321920 : K[X]) * t1 ^ 4 * H ^ 2) + (41287680 : K[X]) * t1 ^ 3 *
      g1 ^ 2 * H - (10813440 : K[X]) * t1 ^ 2 * t2 * g1 * H + (5898240 :
      K[X]) * t1 ^ 2 * u * H ^ 2 - (6881280 : K[X]) * t1 ^ 2 * t3 * g1 * H
      ^ 2 - (5898240 : K[X]) * t1 ^ 2 * g1 ^ 4 + (655360 : K[X]) * t1 * t2
      ^ 2 * H + (655360 : K[X]) * t1 * t2 * t3 * H ^ 2 + (1966080 : K[X])
      * t1 * t2 * g1 ^ 3 - (8847360 : K[X]) * t1 * u * g1 ^ 2 * H +
      (655360 : K[X]) * t1 * t3 ^ 2 * H ^ 3 + (983040 : K[X]) * t1 * t3 *
      g1 ^ 3 * H + (1433272320 : K[X]) * t1 * g1 * a1 * H - (2149908480 :
      K[X]) * t1 * a0 * H ^ 2 - (163840 : K[X]) * t2 ^ 2 * g1 ^ 2 +
      (983040 : K[X]) * t2 * u * g1 * H - (163840 : K[X]) * t2 * t3 * g1 ^
      2 * H - (119439360 : K[X]) * t2 * a1 * H - (491520 : K[X]) * u ^ 2 *
      H ^ 2 + (983040 : K[X]) * u * t3 * g1 * H ^ 2 - (163840 : K[X]) * t3
      ^ 2 * g1 ^ 2 * H ^ 2 - (119439360 : K[X]) * t3 * a1 * H ^ 2 -
      Polynomial.C κ₇ * ((384 : K[X]) * H ^ 2) + Polynomial.C κ₅ * ((12288
      : K[X]) * t1 * H ^ 2) + Polynomial.C κ * ((5898240 : K[X]) * t1 ^ 3
      * H ^ 2) - Polynomial.C κ * ((11796480 : K[X]) * t1 ^ 2 * g1 ^ 2 *
      H) + Polynomial.C κ * ((2752512 : K[X]) * t1 * t2 * g1 * H) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * u * H ^ 2) + Polynomial.C
      κ * ((1966080 : K[X]) * t1 * t3 * g1 * H ^ 2) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 2 * H) - Polynomial.C κ * ((131072 : K[X]) *
      t2 * t3 * H ^ 2) + Polynomial.C κ * ((1179648 : K[X]) * u * g1 ^ 2 *
      H) - Polynomial.C κ * ((131072 : K[X]) * t3 ^ 2 * H ^ 3) -
      Polynomial.C κ * ((286654464 : K[X]) * g1 * a1 * H) + Polynomial.C κ
      * ((859963392 : K[X]) * a0 * H ^ 2))) * ht3
  simp only [alignedEleventhNonsquareResidue610]
  apply mul_left_cancel₀ (mul_ne_zero
    (show (-128 : K[X]) ≠ 0 by norm_num) (pow_ne_zero 2 hH))
  linear_combination hR4n + (-((5898240 : K[X]) * t1 ^ 3 * H - (2949120 : K[X]) * t1 * u * H +
    (2949120 : K[X]) * t1 * t3 * g1 * H + (1474560 : K[X]) * u * g1 ^ 2 -
    (491520 : K[X]) * t3 ^ 2 * H ^ 2 - (1474560 : K[X]) * v * g1 * H -
    (358318080 : K[X]) * g1 * a1 + (2149908480 : K[X]) * a0 * H -
    Polynomial.C κ₅ * ((12288 : K[X]) * H) - Polynomial.C κ * ((3538944 :
    K[X]) * t1 ^ 2 * H) + Polynomial.C κ * ((1179648 : K[X]) * u * H) -
    Polynomial.C κ * ((1179648 : K[X]) * t3 * g1 * H))) * hv

end Max11DegreeRoutes
