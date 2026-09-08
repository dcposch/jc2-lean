import LowScale68SecondaryExtractionPart02Scratch

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

def cubicLoadVPolynomial68
    (l alpha beta gamma delta epsilon eta : k)
    (A B c D e : k[X]) : k[X] :=
  (-7 / 432 * l : k) • (A ^ 2 * B) +
    (7 / 36 * l : k) • (A * D) + (7 / 36 * l : k) • (B * c) +
    (1 / 27 * alpha : k) • A ^ 3 +
    (1 / 3 * alpha : k) • (A * c) + alpha • e -
    (5 / 36 * beta : k) • (A * B) + (5 / 6 * beta : k) • D +
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
    (1 / 2 * delta : k) • B + (1 / 3 * epsilon : k) • A + C eta

/-- Exact decomposition of all four integrated coefficients into their
load-free cubic part and lower-weight load part. -/
structure CubicIntegratedCoordinates68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : Prop where
  s_eq : integratedSPolynomial68 l alpha beta delta A B
      ((1 / 3 : k) • A ^ 2 + c) D =
    cubicHomogeneousSPolynomial68 A B D +
      cubicLoadSPolynomial68 l alpha beta delta A B c
  t_eq : integratedTPolynomial68 l alpha beta gamma epsilon A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousTPolynomial68 A B c e +
      cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  u_eq : integratedUPolynomial68 l alpha beta gamma delta zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousUPolynomial68 A B c D +
      cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  v_eq : integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousVPolynomial68 A B c D e +
      cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta A B c D e

set_option maxHeartbeats 4000000 in
theorem integratedPolynomial68_cubicCoordinates
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    CubicIntegratedCoordinates68 l alpha beta gamma delta epsilon zeta eta
      A B c D e := by
  constructor <;>
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) <;>
    simp only [integratedSPolynomial68, integratedTPolynomial68,
      integratedUPolynomial68, integratedVPolynomial68,
      cubicHomogeneousSPolynomial68, cubicHomogeneousTPolynomial68,
      cubicHomogeneousUPolynomial68, cubicHomogeneousVPolynomial68,
      cubicLoadSPolynomial68, cubicLoadTPolynomial68,
      cubicLoadUPolynomial68, cubicLoadVPolynomial68,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      RatFunc.algebraMap_C] <;>
    simp only [map_neg, map_div₀, map_ofNat, map_one] <;>
    ring

/-- Exact load-free first one-form after the cubic translation. -/
def cubicHomogeneousRowTwoPolynomial68 (A B c D e : k[X]) : k[X] :=
  lowerRowTwoPolynomial68
    (cubicHomogeneousSPolynomial68 A B D)
    (cubicHomogeneousTPolynomial68 A B c e)
    (cubicHomogeneousUPolynomial68 A B c D)
    (cubicHomogeneousVPolynomial68 A B c D e)
    B ((1 / 3 : k) • A ^ 2 + c) D
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

/-- Contribution of the constant-load pieces to the first one-form row. -/
def cubicLoadRowTwoPolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl

end SecondaryExtraction68
end Max11DegreeRoutes
