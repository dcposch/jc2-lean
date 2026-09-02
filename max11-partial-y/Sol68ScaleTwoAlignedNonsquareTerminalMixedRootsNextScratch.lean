import Sol68ScaleTwoAlignedNonsquareTerminalMixedRootsScratch

/-! # The next compatibility polynomial on the mixed-root locus -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalRZeroNextAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalRZeroI4Next68
    (h hh rd rdd x xd y yd u ud v vd z gamma epsilon : k) : k :=
  20 * h ^ 2 * x ^ 3 * y - 75816 * h ^ 2 * x ^ 2 * v -
    486 * h ^ 2 * x * y * gamma - 648 * h * xd * y * u +
    1296 * h * x * yd * u - 648 * h * x * y * ud +
    972 * h * rd * y * v + 2916 * h ^ 2 * y * z +
    2187 * h ^ 2 * y * epsilon - 13122 * rdd * u ^ 2 +
    39366 * hh * u * v - 78732 * h * ud * v + 78732 * h * u * vd

def terminalRZeroLastNext68
    (h hh y u ud v vd rdd : k) : k :=
  h ^ 2 * y * v ^ 2 - 6 * rdd * u ^ 3 + 18 * hh * u ^ 2 * v -
    36 * h * u * ud * v + 36 * h * u ^ 2 * vd

def terminalRZeroNextCompatibility68
    (h rd x xd y yd u ud v z gamma epsilon : k) : k :=
  20 * h * x ^ 3 * y * u - 75816 * h * x ^ 2 * u * v -
    486 * h * x * y * u * gamma - 648 * xd * y * u ^ 2 +
    1296 * x * yd * u ^ 2 - 648 * x * y * u * ud +
    972 * rd * y * u * v - 2187 * h * y * v ^ 2 +
    2916 * h * y * u * z + 2187 * h * y * u * epsilon

/-- Eliminating the sole fresh `p₁'` jet between the next two rows. -/
theorem terminalRZero_nextRows_compatibility_68
    (h hh rd rdd x xd y yd u ud v vd z gamma epsilon : k)
    (hh0 : h ≠ 0) (hu : u ≠ 0)
    (hI : terminalRZeroI4Next68 h hh rd rdd x xd y yd u ud v vd z
      gamma epsilon = 0)
    (hR : terminalRZeroLastNext68 h hh y u ud v vd rdd = 0) :
    terminalRZeroNextCompatibility68 h rd x xd y yd u ud v z
      gamma epsilon = 0 := by
  have hscaled : 36 * h ^ 2 * u *
      terminalRZeroNextCompatibility68 h rd x xd y yd u ud v z
        gamma epsilon = 0 := by
    dsimp only [terminalRZeroI4Next68] at hI
    dsimp only [terminalRZeroLastNext68] at hR
    dsimp only [terminalRZeroNextCompatibility68]
    linear_combination (36 * h * u ^ 2) * hI - (78732 * h * u) * hR
  have hc : 36 * h ^ 2 * u ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hh0)) hu
  exact (mul_eq_zero.mp hscaled).resolve_left hc

/-- The compatibility is affine with a nonzero coefficient in the first
remaining `p₀` value, explaining why this order refines but does not itself
contradict the mixed branch. -/
theorem terminalRZero_nextCompatibility_pZero_coefficient_ne_68
    (h y u : k) (hh : h ≠ 0) (hy : y ≠ 0) (hu : u ≠ 0) :
    2916 * h * y * u ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh) hy) hu

end TerminalRZeroNextAlgebra68

section TerminalRZeroNextReducedRows68

variable {k : Type*} [Field k] [CharZero k]

/-- Second derivative of the quotient `I₄` row after imposing the rigid
mixed-root first-jet packet. -/
theorem terminalRZero_reduced_I4_secondDerivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0) :
    ((((terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2).derivative).derivative).eval a) =
      (4 / 59049 : k) * terminalRZeroI4Next68
        (H.derivative.eval a) (H.derivative.derivative.eval a)
        (r.derivative.eval a) (r.derivative.derivative.eval a)
        (X.eval a) (X.derivative.eval a) (Yd.eval a) (Yd.derivative.eval a)
        (p2.eval a) (p2.derivative.eval a) (p1.eval a)
        (p1.derivative.eval a) (p0.eval a) gamma epsilon := by
  have hv : p1.eval a =
      r.derivative.eval a * p2.eval a / (3 * H.derivative.eval a) := by
    field_simp [hh]
    linear_combination hlin
  have hx : X.eval a = -(Yd.eval a) ^ 2 / (1458 * p2.eval a) := by
    field_simp [hu]
    linear_combination hquad
  simp only [terminalGReducedB68, terminalGReducedPhi68,
    terminalGReducedW68, terminalGReducedD68, terminalRZeroI4Next68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
    eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, ha, hr, zero_mul, mul_zero, zero_add, add_zero, zero_pow]
  rw [hv, hx]
  field_simp [hh, hu]
  ring

/-- Honest handoff after the checked `I₄` transport.  The sole remaining
mechanical input is the displayed scalar third-last-row coefficient, stated
as a proposition rather than postulated as an axiom. -/
theorem terminalRZero_reduced_nextCompatibility_of_lastNext_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0)
    (hI4 : terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2 = 0)
    (hLastNext : terminalRZeroLastNext68
      (H.derivative.eval a) (H.derivative.derivative.eval a)
      (Yd.eval a) (p2.eval a) (p2.derivative.eval a)
      (p1.eval a) (p1.derivative.eval a)
      (r.derivative.derivative.eval a) = 0) :
    terminalRZeroNextCompatibility68
      (H.derivative.eval a) (r.derivative.eval a) (X.eval a)
      (X.derivative.eval a) (Yd.eval a) (Yd.derivative.eval a)
      (p2.eval a) (p2.derivative.eval a) (p1.eval a) (p0.eval a)
      gamma epsilon = 0 := by
  have hI4second :
      ((((terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2).derivative).derivative).eval a) =
        0 := by
    rw [hI4, derivative_zero, derivative_zero, eval_zero]
  have hIfactor := terminalRZero_reduced_I4_secondDerivative_factor_68
    H r X Yd p0 p1 p2 gamma epsilon a ha hr hh hu hlin hquad
  rw [hI4second] at hIfactor
  have hInext : terminalRZeroI4Next68
      (H.derivative.eval a) (H.derivative.derivative.eval a)
      (r.derivative.eval a) (r.derivative.derivative.eval a)
      (X.eval a) (X.derivative.eval a) (Yd.eval a) (Yd.derivative.eval a)
      (p2.eval a) (p2.derivative.eval a) (p1.eval a)
      (p1.derivative.eval a) (p0.eval a) gamma epsilon = 0 := by
    have hc : (4 / 59049 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hIfactor.symm).resolve_left hc
  exact terminalRZero_nextRows_compatibility_68
    (H.derivative.eval a) (H.derivative.derivative.eval a)
    (r.derivative.eval a) (r.derivative.derivative.eval a)
    (X.eval a) (X.derivative.eval a) (Yd.eval a) (Yd.derivative.eval a)
    (p2.eval a) (p2.derivative.eval a) (p1.eval a)
    (p1.derivative.eval a) (p0.eval a) gamma epsilon hh hu hInext hLastNext

end TerminalRZeroNextReducedRows68

end Max11DegreeRoutes
