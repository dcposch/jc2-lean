import LowScale68SecondaryFirstLoadWallFace

/-! # Literal coefficient cores on the `(6,8)` wall `2g = n`

This module checks the invariant and homogeneous one-form coefficients, the
pure `l` Jacobian cores, and the load-free row-one coefficient on the first
loaded equality wall.  The remaining bridge is the core-plus-remainder split
for the full row-two and row-zero load polynomials.
-/

noncomputable section

namespace Max11DegreeRoutes

/-! ## Polynomial coefficient extraction on `2g = n`

The formulas below re-prove the mixed leading coefficients of §3.3 by the
same `coeff_mul_at_bounds68` / `coeff_derivative_at_bound68` style as the
tracked first-face extraction.  Derivative substitutions are the coefficient
identity `(p').coeff(u-1) = u * p.coeff u`, which holds for constant
coordinates as well (both sides vanish).  On this wall every displayed
bound is positive: `2g = n` and `0 < n` force `n ≥ 2`. -/

section FirstLoadWallExtraction68

open Polynomial

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Jacobian load cores, with the `A^5` cancellation checked by `ring` -/

/-- The unique `l A^5` combination in row two: `Ul C0' + 3 Sl E' - 2 C0 Ul'`
on the cubic core `C0 = A^2/3`, `E = A^3/27`. -/
def cubicLoadRowTwoLCorePolynomial68 (l : k) (A : k[X]) : k[X] :=
  let C0 := (1 / 3 : k) • A ^ 2
  let E := (1 / 27 : k) • A ^ 3
  let Ul := (35 / 432 * l : k) • A ^ 3
  let Sl := (35 / 72 * l : k) • A ^ 2
  Ul * derivative C0 + (3 : k) • (Sl * derivative E) -
    (2 : k) • (C0 * derivative Ul)

/-- The unique `l A^6` combination in row zero: `Ul E'` on `E = A^3/27`. -/
def cubicLoadRowZeroLCorePolynomial68 (l : k) (A : k[X]) : k[X] :=
  ((35 / 432 * l : k) • A ^ 3) *
    derivative ((1 / 27 : k) • A ^ 3)

set_option maxHeartbeats 4000000 in
/-- `3 Sl E'` and `-2 C0 Ul'` cancel; only `Ul C0' = (35/648) l A^4 A'`
survives. -/
theorem cubicLoadRowTwoLCorePolynomial68_eq (l : k) (A : k[X]) :
    cubicLoadRowTwoLCorePolynomial68 l A =
      (35 / 648 * l : k) • (A ^ 4 * derivative A) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoLCorePolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroLCorePolynomial68_eq (l : k) (A : k[X]) :
    cubicLoadRowZeroLCorePolynomial68 l A =
      (35 / 3888 * l : k) • (A ^ 5 * derivative A) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowZeroLCorePolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoLCorePolynomial68_coeff_loadWall
    (l : k) (A : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadRowTwoLCorePolynomial68 l A).coeff (10 * n - 1) =
      (35 / 324 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  have hA4deg : (A ^ 4).natDegree ≤ 8 * n := by
    compute_degree
    omega
  have hA4 : (A ^ 4).coeff (8 * n) = A.coeff (2 * n) ^ 4 := by
    have h := coeff_pow_at_bound68 A (2 * n) 4 hA
    have hi : 4 * (2 * n) = 8 * n := by omega
    simpa only [hi] using h
  have hprod : (A ^ 4 * derivative A).coeff (10 * n - 1) =
      A.coeff (2 * n) ^ 4 * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 (A ^ 4) A
      (8 * n) (2 * n) (by omega) hA4deg hA
    have hi : 8 * n + 2 * n - 1 = 10 * n - 1 := by omega
    rw [hi, hA4] at h
    exact h
  rw [cubicLoadRowTwoLCorePolynomial68_eq, coeff_smul, hprod, smul_eq_mul]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroLCorePolynomial68_coeff_loadWall
    (l : k) (A : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadRowZeroLCorePolynomial68 l A).coeff (12 * n - 1) =
      (35 / 1944 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  have hA5deg : (A ^ 5).natDegree ≤ 10 * n := by
    compute_degree
    omega
  have hA5 : (A ^ 5).coeff (10 * n) = A.coeff (2 * n) ^ 5 := by
    have h := coeff_pow_at_bound68 A (2 * n) 5 hA
    have hi : 5 * (2 * n) = 10 * n := by omega
    simpa only [hi] using h
  have hprod : (A ^ 5 * derivative A).coeff (12 * n - 1) =
      A.coeff (2 * n) ^ 5 * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 (A ^ 5) A
      (10 * n) (2 * n) (by omega) hA5deg hA
    have hi : 10 * n + 2 * n - 1 = 12 * n - 1 := by omega
    rw [hi, hA5] at h
    exact h
  rw [cubicLoadRowZeroLCorePolynomial68_eq, coeff_smul, hprod, smul_eq_mul]
  push_cast
  ring

/-! ### Mixed I4 at `8n` and load-free I3 at `9n` -/

end FirstLoadWallExtraction68
end Max11DegreeRoutes
