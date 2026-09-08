import LowScale68SecondaryOneFormsPart04Scratch

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

/-- Exact load-free terminal one-form after the cubic translation. -/
def cubicHomogeneousRowZeroPolynomial68 (A B c D e : k[X]) : k[X] :=
  lowerRowZeroPolynomial68
    (cubicHomogeneousUPolynomial68 A B c D)
    (cubicHomogeneousVPolynomial68 A B c D e) D
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

/-- Deficit-two part of the load-free terminal one-form. -/
def firstSecondaryCoreRowZeroPolynomial68 (A B c D e : k[X]) : k[X] :=
  (4 / 81 : k) •
    (A ^ 2 * B * c * derivative A -
      (3 : k) • (A * D * c * derivative A) -
      (9 : k) • (D * e * derivative A))

/-- Deficit-three remainder of the load-free terminal one-form. -/
def cubicRemainderRowZeroPolynomial68 (A B c D e : k[X]) : k[X] :=
  (4 / 81 : k) •
    ((6 : k) • (A * B * D * derivative B) +
      (3 : k) • (A * B * c * derivative c) +
      (3 : k) • (B ^ 2 * D * derivative A) +
      (3 : k) • (B * c ^ 2 * derivative A) -
      (9 : k) • (B * D * derivative D) +
      (9 : k) • (B * c * derivative e) -
      (9 : k) • (D ^ 2 * derivative B) -
      (9 : k) • (D * c * derivative c))

/-- Fully expanded load-free terminal row. -/
def cubicHomogeneousRowZeroExpandedPolynomial68
    (A B c D e : k[X]) : k[X] :=
  firstSecondaryCoreRowZeroPolynomial68 A B c D e +
    cubicRemainderRowZeroPolynomial68 A B c D e

set_option maxHeartbeats 4000000 in
theorem cubicHomogeneousRowZeroPolynomial68_eq_expanded
    (A B c D e : k[X]) :
    cubicHomogeneousRowZeroPolynomial68 A B c D e =
      cubicHomogeneousRowZeroExpandedPolynomial68 A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowZeroPolynomial68,
    cubicHomogeneousRowZeroExpandedPolynomial68,
    firstSecondaryCoreRowZeroPolynomial68,
    cubicRemainderRowZeroPolynomial68,
    cubicHomogeneousUPolynomial68, cubicHomogeneousVPolynomial68,
    lowerRowZeroPolynomial68, derivative_add, derivative_sub,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

end SecondaryOneForms68
end Max11DegreeRoutes
