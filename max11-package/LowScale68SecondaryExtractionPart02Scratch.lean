import LowScale68SecondaryExtractionPart01Scratch

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

/-- Compact polynomial form of the first invariant after translating away the
even cubic core. -/
def cubicFirstIntegralFourPolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) : k[X] :=
  (-8 / 27 : k) • B ^ 3 - (8 / 9 : k) • (A * B * c) +
    (8 / 3 : k) • (B * e) + (8 / 3 : k) • (D * c) + zeta • A +
    (2 * epsilon : k) • B + (1 / 4 * delta : k) • A ^ 2 +
    (3 * delta : k) • c + (4 * gamma : k) • D -
    (4 / 3 * gamma : k) • (A * B) + (5 * beta : k) • e +
    (5 / 6 * beta : k) • (A * c) - (5 / 12 * beta : k) • B ^ 2 +
    (5 / 72 * beta : k) • A ^ 3 + (35 / 1728 * l : k) • A ^ 4 +
    (7 / 24 * l : k) • (A ^ 2 * c) -
    (35 / 72 * l : k) • (A * B ^ 2) +
    (7 / 6 * l : k) • (A * e) + (7 / 6 * l : k) • (B * D) +
    (7 / 12 * l : k) • c ^ 2

/-- Compact polynomial form of the second invariant in the same transverse
coordinates. -/
def cubicFirstIntegralThreePolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) : k[X] :=
  (4 / 9 : k) • (A ^ 2 * B ^ 2) - (16 / 9 : k) • (A * B * D) -
    (8 / 9 : k) • (B ^ 2 * c) + (4 / 3 : k) • D ^ 2 +
    (8 / 3 : k) • (c * e) + zeta • B + (2 * epsilon : k) • c +
    (4 * gamma : k) • e - (2 / 3 * gamma : k) • B ^ 2 +
    (3 * delta : k) • D - (3 / 2 * delta : k) • (A * B) +
    (5 / 24 * beta : k) • (A ^ 2 * B) -
    (5 / 6 * beta : k) • (A * D) -
    (5 / 6 * beta : k) • (B * c) +
    (7 / 432 * l : k) • (A ^ 3 * B) -
    (7 / 72 * l : k) • (A ^ 2 * D) -
    (7 / 12 * l : k) • (A * B * c) -
    (35 / 216 * l : k) • B ^ 3 +
    (7 / 6 * l : k) • (B * e) + (7 / 6 * l : k) • (D * c)

/-- The terms of the first one-form row that can attain secondary deficit
two.  Every omitted homogeneous term has at least three transverse factors,
and every omitted load term has lower old weight in the chamber `2g<n`. -/
def firstSecondaryCoreRowTwoPolynomial68
    (A B c D e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((2 : k) • (A ^ 2 * B * derivative c) +
      (2 : k) • (A ^ 2 * c * derivative B) +
      A * B * c * derivative A -
      (6 : k) • (A * D * derivative c) -
      (6 : k) • (A * c * derivative D) +
      (9 : k) • (B * e * derivative A) +
      (3 : k) • (D * c * derivative A) -
      (18 : k) • (D * derivative e) -
      (18 : k) • (e * derivative D))

/-- Load-free integrated coefficients on the cubic-coordinate chart. -/
def cubicHomogeneousSPolynomial68 (A B D : k[X]) : k[X] :=
  (4 / 9 : k) • (A * B) + (4 / 3 : k) • D

def cubicHomogeneousTPolynomial68 (A B c e : k[X]) : k[X] :=
  (4 / 27 : k) • A ^ 3 + (8 / 9 : k) • (A * c) +
    (2 / 9 : k) • B ^ 2 + (4 / 3 : k) • e

def cubicHomogeneousUPolynomial68 (A B c D : k[X]) : k[X] :=
  (4 / 9 : k) • (A * D) + (4 / 9 : k) • (B * c)

def cubicHomogeneousVPolynomial68 (A B c D e : k[X]) : k[X] :=
  (1 / 81 : k) • A ^ 4 + (4 / 27 : k) • (A ^ 2 * c) -
    (4 / 27 : k) • (A * B ^ 2) + (4 / 9 : k) • (B * D) +
    (4 / 9 : k) • (A * e) + (2 / 9 : k) • c ^ 2

/-- The complementary constant-load pieces of the four integrated
coefficients in cubic coordinates. -/
def cubicLoadSPolynomial68
    (l alpha beta delta : k) (A B c : k[X]) : k[X] :=
  (35 / 72 * l : k) • A ^ 2 + (7 / 6 * l : k) • c +
    alpha • B + (5 / 6 * beta : k) • A + C delta

def cubicLoadTPolynomial68
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) : k[X] :=
  (7 / 36 * l : k) • (A * B) + (7 / 6 * l : k) • D +
    (1 / 3 * alpha : k) • A ^ 2 + alpha • c +
    (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon

def cubicLoadUPolynomial68
    (l alpha beta gamma delta zeta : k)
    (A B c D e : k[X]) : k[X] :=
  (35 / 432 * l : k) • A ^ 3 + (7 / 12 * l : k) • (A * c) +
    (7 / 72 * l : k) • B ^ 2 + (7 / 6 * l : k) • e +
    alpha • D + (5 / 24 * beta : k) • A ^ 2 +
    (5 / 6 * beta : k) • c + (2 / 3 * gamma : k) • B +
    (1 / 2 * delta : k) • A + C zeta

end SecondaryExtraction68
end Max11DegreeRoutes
