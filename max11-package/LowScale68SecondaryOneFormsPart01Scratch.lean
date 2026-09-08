import LowScale68SecondaryExtraction

/-! # The last two `(6,8)` secondary one-form equations

The preceding extraction module handles both invariants and the first
one-form row.  This module performs the same load-free/load decomposition for
the remaining two rows and connects their literal polynomial coefficients to
`F1` and `F0` of `FirstSecondaryFace68`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryOneForms68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact load-free second one-form after the cubic translation. -/
def cubicHomogeneousRowOnePolynomial68 (A B c D e : k[X]) : k[X] :=
  lowerRowOnePolynomial68
    (cubicHomogeneousTPolynomial68 A B c e)
    (cubicHomogeneousUPolynomial68 A B c D)
    (cubicHomogeneousVPolynomial68 A B c D e)
    ((1 / 3 : k) • A ^ 2 + c) D
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

/-- Deficit-two part of the load-free second one-form. -/
def firstSecondaryCoreRowOnePolynomial68 (A B c D e : k[X]) : k[X] :=
  (-4 / 81 : k) •
    (-(4 : k) • (A ^ 3 * B * derivative B) -
      (3 : k) • (A ^ 2 * B ^ 2 * derivative A) +
      (6 : k) • (A ^ 2 * B * derivative D) +
      (6 : k) • (A ^ 2 * D * derivative B) -
      (18 : k) • (A * c * derivative e) -
      (18 : k) • (A * e * derivative c) +
      (9 : k) • (D ^ 2 * derivative A) -
      (54 : k) • (e * derivative e))

/-- Deficit-three remainder of the load-free second one-form. -/
def cubicRemainderRowOnePolynomial68 (A B c D e : k[X]) : k[X] :=
  (-4 / 81 : k) •
    (-(3 : k) • (A * B ^ 2 * derivative c) -
      (12 : k) • (A * B * c * derivative B) -
      (9 : k) • (B ^ 2 * c * derivative A) -
      (9 : k) • (B ^ 2 * derivative e) +
      (9 : k) • (B * D * derivative c) +
      (9 : k) • (B * c * derivative D) +
      (27 : k) • (D * c * derivative B) +
      (18 : k) • (c ^ 2 * derivative c))

/-- Fully expanded load-free second row. -/
def cubicHomogeneousRowOneExpandedPolynomial68
    (A B c D e : k[X]) : k[X] :=
  firstSecondaryCoreRowOnePolynomial68 A B c D e +
    cubicRemainderRowOnePolynomial68 A B c D e

set_option maxHeartbeats 4000000 in
theorem cubicHomogeneousRowOnePolynomial68_eq_expanded
    (A B c D e : k[X]) :
    cubicHomogeneousRowOnePolynomial68 A B c D e =
      cubicHomogeneousRowOneExpandedPolynomial68 A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowOnePolynomial68,
    cubicHomogeneousRowOneExpandedPolynomial68,
    firstSecondaryCoreRowOnePolynomial68,
    cubicRemainderRowOnePolynomial68,
    cubicHomogeneousTPolynomial68, cubicHomogeneousUPolynomial68,
    cubicHomogeneousVPolynomial68, lowerRowOnePolynomial68,
    derivative_add, derivative_sub, derivative_smul, derivative_mul,
    derivative_pow, derivative_C, Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

end SecondaryOneForms68
end Max11DegreeRoutes
