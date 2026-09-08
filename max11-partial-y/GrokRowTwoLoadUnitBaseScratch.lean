import LowScale68SecondaryExtraction

/-! Scratch kernel check of the translated `(6,8)` row-two load.

After `D = A*B/3 + d`, the constant-load first one-form collapses to the
six-parameter expansion recorded by
`cases/max11_68_row2_load_reduction_20260828.py`.  The scalars `alpha` and
`eta` cancel identically.  The identity is proved by linearity in the load
parameters plus eight unit expansions, so `ring` never sees all eight
scalars at once.  The simplified form is then below the `3g` cutoff.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RowTwoLoadScratch

variable {k : Type*} [Field k] [CharZero k]

/-- Exact load contribution to the first one-form after `D=A*B/3+d`.
The coefficients are the factored CAS expansion; `alpha` and `eta` are
absent because they cancel. -/
def cubicLoadRowTwoTranslatedPolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c d e : k[X]) : k[X] :=
  (7 / 1296 * l : k) •
    ((10 : k) • (A ^ 4 * derivative A) +
      (33 : k) • (A ^ 3 * derivative c) -
      (15 : k) • (A ^ 2 * B * derivative B) +
      (72 : k) • (A ^ 2 * c * derivative A) +
      (126 : k) • (A ^ 2 * derivative e) -
      (6 : k) • (A * B ^ 2 * derivative A) +
      (36 : k) • (A * B * derivative d) +
      (108 : k) • (A * c * derivative c) +
      (36 : k) • (A * d * derivative B) +
      (144 : k) • (A * e * derivative A) -
      (90 : k) • (B ^ 2 * derivative c) -
      (180 : k) • (B * c * derivative B) -
      (72 : k) • (B * d * derivative A) +
      (216 : k) • (c * derivative e) +
      (216 : k) • (d * derivative d) +
      (216 : k) • (e * derivative c)) +
  (5 / 72 * beta : k) •
    ((2 : k) • (A ^ 3 * derivative A) +
      (7 : k) • (A ^ 2 * derivative c) -
      (2 : k) • (A * B * derivative B) +
      (8 : k) • (A * c * derivative A) +
      (36 : k) • (A * derivative e) +
      (2 : k) • (B ^ 2 * derivative A) -
      (12 : k) • (B * derivative d) -
      (12 : k) • (c * derivative c) -
      (12 : k) • (d * derivative B)) +
  (2 / 3 * gamma : k) •
    ((2 : k) • (A * derivative d) -
      (2 : k) • (B * derivative c) -
      (2 : k) • (c * derivative B) -
      d * derivative A) +
  (1 / 6 * delta : k) •
    ((2 : k) • (A ^ 2 * derivative A) +
      (9 : k) • (A * derivative c) -
      (9 : k) • (B * derivative B) +
      (18 : k) • derivative e) +
  (1 / 3 * epsilon : k) •
    ((2 : k) • (A * derivative B) -
      B * derivative A +
      (6 : k) • derivative d) +
  (1 / 3 * zeta : k) •
    ((2 : k) • (A * derivative A) +
      (3 : k) • derivative c)

/-- Common unfolding for a unit-parameter translated-load identity. -/
macro "row_two_load_unit_ring" : tactic => `(tactic|
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring)

end RowTwoLoadScratch

end Max11DegreeRoutes

