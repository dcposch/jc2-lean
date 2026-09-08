import LowScale68SecondaryExtractionPart03Scratch

/-! # Extracting the first `(6,8)` secondary face

This module connects the abstract scalar face classified in
`LowScale68SecondaryFace` to the literal polynomial lower system.  The four
transverse coordinates have different secondary degree bounds, so the usual
single weighted-boundary lemmas are first replaced by arbitrary-bound
coefficient rules.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryExtraction68

variable {k : Type*} [Field k] [CharZero k]

/-- Linearity of the first one-form row under the homogeneous/load split. -/
theorem cubicRowTwoPolynomial68_split
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    lowerRowTwoPolynomial68
      (cubicHomogeneousSPolynomial68 A B D +
        cubicLoadSPolynomial68 l alpha beta delta A B c)
      (cubicHomogeneousTPolynomial68 A B c e +
        cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D)
      (cubicHomogeneousUPolynomial68 A B c D +
        cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e)
      (cubicHomogeneousVPolynomial68 A B c D e +
        cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta A B c D e)
      B ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousRowTwoPolynomial68 A B c D e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e := by
  simp only [cubicHomogeneousRowTwoPolynomial68,
    cubicLoadRowTwoPolynomial68, lowerRowTwoPolynomial68, derivative_add,
    Polynomial.smul_eq_C_mul]
  ring

/-- Fully expanded load-free row, grouped before degree extraction. -/
def cubicHomogeneousRowTwoExpandedPolynomial68
    (A B c D e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((2 : k) • (A ^ 2 * B * derivative c) +
      (2 : k) • (A ^ 2 * c * derivative B) +
      A * B * c * derivative A -
      (6 : k) • (A * B ^ 2 * derivative B) -
      (6 : k) • (A * D * derivative c) -
      (6 : k) • (A * c * derivative D) -
      (3 : k) • (B ^ 3 * derivative A) +
      (9 : k) • (B * e * derivative A) +
      (3 : k) • (D * c * derivative A) +
      (6 : k) • (B ^ 2 * derivative D) +
      (12 : k) • (B * D * derivative B) +
      (12 : k) • (B * c * derivative c) +
      (6 : k) • (c ^ 2 * derivative B) -
      (18 : k) • (D * derivative e) -
      (18 : k) • (e * derivative D))

/-- The terms of secondary deficit three in the load-free first row. -/
def cubicRemainderRowTwoPolynomial68 (A B c D : k[X]) : k[X] :=
  (-4 / 27 : k) •
    (-(6 : k) • (A * B ^ 2 * derivative B) -
      (3 : k) • (B ^ 3 * derivative A) +
      (6 : k) • (B ^ 2 * derivative D) +
      (12 : k) • (B * D * derivative B) +
      (12 : k) • (B * c * derivative c) +
      (6 : k) • (c ^ 2 * derivative B))

theorem cubicHomogeneousRowTwoExpandedPolynomial68_split
    (A B c D e : k[X]) :
    cubicHomogeneousRowTwoExpandedPolynomial68 A B c D e =
      firstSecondaryCoreRowTwoPolynomial68 A B c D e +
        cubicRemainderRowTwoPolynomial68 A B c D := by
  simp only [cubicHomogeneousRowTwoExpandedPolynomial68,
    firstSecondaryCoreRowTwoPolynomial68, cubicRemainderRowTwoPolynomial68]
  module

set_option maxHeartbeats 4000000 in
theorem cubicHomogeneousRowTwoPolynomial68_eq_expanded
    (A B c D e : k[X]) :
    cubicHomogeneousRowTwoPolynomial68 A B c D e =
      cubicHomogeneousRowTwoExpandedPolynomial68 A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowTwoPolynomial68,
    cubicHomogeneousRowTwoExpandedPolynomial68,
    cubicHomogeneousSPolynomial68, cubicHomogeneousTPolynomial68,
    cubicHomogeneousUPolynomial68, cubicHomogeneousVPolynomial68,
    lowerRowTwoPolynomial68, derivative_add, derivative_sub,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

end SecondaryExtraction68
end Max11DegreeRoutes
