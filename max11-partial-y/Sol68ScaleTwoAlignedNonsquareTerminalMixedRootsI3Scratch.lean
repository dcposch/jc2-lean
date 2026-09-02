import Sol68ScaleTwoAlignedNonsquareTerminalMixedRootsLastBridgeScratch

/-! # The independent constant-I3 coefficient on the mixed-root locus -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section ScaledI3Algebra68

variable {F : Type*} [Field F] [CharZero F]

/-- Weight-ten clearing of the aligned constant `I₃`.  Here `H=h²`, while
`A,B,C,D,E` have respective cleared weights `2,3,4,5,6`. -/
def terminalGReducedI3Scaled68
    (H A B C0 D E gamma epsilon : F) : F :=
  (-16 / 243 : F) * A ^ 5 + (4 / 3 : F) * D ^ 2 +
    2 * H ^ 3 * C0 * epsilon + 4 * H ^ 2 * E * gamma -
    (8 / 9 : F) * A * C0 ^ 2 - (8 / 9 : F) * B ^ 2 * C0 -
    (8 / 9 : F) * A ^ 2 * E - (2 / 3 : F) * H ^ 3 * A ^ 2 * epsilon -
    (2 / 3 : F) * H ^ 2 * B ^ 2 * gamma + (8 / 3 : F) * C0 * E +
    (8 / 27 : F) * H ^ 2 * A ^ 3 * gamma +
    (20 / 27 : F) * A ^ 2 * B ^ 2 + (40 / 81 : F) * A ^ 3 * C0 -
    (16 / 9 : F) * A * B * D - (4 / 3 : F) * H ^ 2 * A * C0 * gamma

/-- Pure homogeneous clearing of constant `I₃`. -/
theorem terminalI3_scaled_of_coordinates_68
    (h H A B C0 D E a b c d e gamma epsilon i3 : F)
    (hH : h ^ 2 = H)
    (ha : h ^ 2 * A = a) (hb : h ^ 3 * B = b)
    (hc : h ^ 4 * C0 = c) (hd : h ^ 5 * D = d)
    (he : h ^ 6 * E = e)
    (hI3 : firstIntegralThree68 0 A B C0 D E 0 gamma 0 epsilon 0 = i3) :
    terminalGReducedI3Scaled68 H a b c d e gamma epsilon = i3 * H ^ 5 := by
  rw [← hH, ← ha, ← hb, ← hc, ← hd, ← he]
  simp only [terminalGReducedI3Scaled68, firstIntegralThree68] at hI3 ⊢
  rw [← hI3]
  ring

end ScaledI3Algebra68

section ScaledI3Polynomial68

variable {k : Type*} [Field k] [CharZero k]

/-- Base-polynomial version of the weight-ten clearing, with every rational
coefficient embedded from the ground field. -/
def terminalGReducedI3ScaledPolynomial68
    (H A B C0 D E : k[X]) (gamma epsilon : k) : k[X] :=
  C (-16 / 243 : k) * A ^ 5 + C (4 / 3 : k) * D ^ 2 +
    C 2 * H ^ 3 * C0 * C epsilon + C 4 * H ^ 2 * E * C gamma -
    C (8 / 9 : k) * A * C0 ^ 2 - C (8 / 9 : k) * B ^ 2 * C0 -
    C (8 / 9 : k) * A ^ 2 * E - C (2 / 3 : k) * H ^ 3 * A ^ 2 * C epsilon -
    C (2 / 3 : k) * H ^ 2 * B ^ 2 * C gamma + C (8 / 3 : k) * C0 * E +
    C (8 / 27 : k) * H ^ 2 * A ^ 3 * C gamma +
    C (20 / 27 : k) * A ^ 2 * B ^ 2 + C (40 / 81 : k) * A ^ 3 * C0 -
    C (16 / 9 : k) * A * B * D - C (4 / 3 : k) * H ^ 2 * A * C0 * C gamma

end ScaledI3Polynomial68

section ReducedI3Local68

variable {k : Type*} [Field k] [CharZero k]

/-- The first informative (third) derivative of scaled `I₃` at a root with
`r=0`.  The cleared odd coordinates are `H·B` and `H·D`; after using the
rigid quadratic relation this coefficient contains no fresh jet. -/
theorem terminalRZero_reduced_I3_thirdDerivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0) :
    (((terminalGReducedI3ScaledPolynomial68 H
      (terminalGReducedA68 H r X)
      (H * terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (H * terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      gamma epsilon).derivative).derivative).derivative.eval a =
        -(40 / 6561 : k) * (H.derivative.eval a) ^ 3 *
          (Yd.eval a) ^ 2 * p2.eval a := by
  simp only [terminalGReducedI3ScaledPolynomial68, terminalGReducedA68,
    terminalGReducedB68, terminalGReducedC68, terminalGReducedD68,
    terminalGReducedE68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, hr, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  linear_combination
    (-8 / 6561 : k) * (H.derivative.eval a) ^ 3 * p2.eval a * hquad

/-- Constant `I₃` immediately excludes the rigid `r=0,b₁≠0` local branch:
the first coefficient is a product of four known nonzero scalars. -/
theorem terminalRZero_impossible_of_reduced_I3_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon i3 a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hy : Yd.eval a ≠ 0)
    (hu : p2.eval a ≠ 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0)
    (hI3 : terminalGReducedI3ScaledPolynomial68 H
      (terminalGReducedA68 H r X)
      (H * terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (H * terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      gamma epsilon = C i3 * H ^ 5) : False := by
  have hzero :
      (((terminalGReducedI3ScaledPolynomial68 H
        (terminalGReducedA68 H r X)
        (H * terminalGReducedB68 r X Yd)
        (terminalGReducedC68 H r X Yd p2)
        (H * terminalGReducedD68 H r X Yd p1 p2)
        (terminalGReducedE68 H r X Yd p0 p1 p2)
        gamma epsilon).derivative).derivative).derivative.eval a = 0 := by
    rw [hI3]
    simp only [derivative_add, derivative_mul, derivative_pow, derivative_C,
      derivative_ofNat, C_ofNat_poly, eval_add, eval_mul, eval_pow, eval_C,
      eval_ofNat, eval_zero, ha, zero_mul, mul_zero, zero_add, add_zero,
      zero_pow]
    ring
  rw [terminalRZero_reduced_I3_thirdDerivative_factor_68
    H r X Yd p0 p1 p2 gamma epsilon a ha hr hquad] at hzero
  have hne : -(40 / 6561 : k) * (H.derivative.eval a) ^ 3 *
      (Yd.eval a) ^ 2 * p2.eval a ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 3 hh))
        (pow_ne_zero 2 hy)) hu
  exact hne hzero

end ReducedI3Local68

section CubicCoordinatesReduced68

variable {k : Type*} [Field k] [CharZero k]

/-- The five cleared cubic coordinates in the two defect variables `X,Yd`.
This is the algebraic rewrite used after source transport. -/
theorem cubicCoordinates_eq_terminalGReduced_68
    (H r t v p0 p1 p2 X Yd : k[X])
    (hX : (3 : k[X]) * t - r ^ 2 = H * X)
    (hY : (27 : k[X]) * v - r ^ 3 = H * Yd) :
    cubicANumerator68 t r = terminalGReducedA68 H r X ∧
    cubicBNumerator68 v t r = H * terminalGReducedB68 r X Yd ∧
    cubicCNumerator68 H p2 v t r = terminalGReducedC68 H r X Yd p2 ∧
    cubicDNumerator68 H p1 p2 v t r =
      H * terminalGReducedD68 H r X Yd p1 p2 ∧
    cubicENumerator68 H p0 p1 p2 v t r =
      terminalGReducedE68 H r X Yd p0 p1 p2 := by
  have ht : t = C (1 / 3 : k) * (r ^ 2 + H * X) := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hXm := congrArg (algebraMap k[X] (RatFunc k)) hX
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hXm ⊢
    linear_combination (1 / 3 : RatFunc k) * hXm
  have hv : v = C (1 / 27 : k) * (r ^ 3 + H * Yd) := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hYm := congrArg (algebraMap k[X] (RatFunc k)) hY
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hYm ⊢
    linear_combination (1 / 27 : RatFunc k) * hYm
  rw [ht, hv]
  simp only [cubicANumerator68, cubicBNumerator68, cubicCNumerator68,
    cubicDNumerator68, cubicENumerator68, terminalGReducedA68,
    terminalGReducedB68, terminalGReducedC68, terminalGReducedD68,
    terminalGReducedE68]
  repeat' constructor
  all_goals
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
    ring

end CubicCoordinatesReduced68

end Max11DegreeRoutes
