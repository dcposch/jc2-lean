import LowScale68SecondaryFirstLoadWallCorePart01Scratch

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

set_option maxHeartbeats 3000000 in
/-- Mixed I4 leading coefficient at index `8n` on `2g = n`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_loadWall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (8 * n) =
      firstLoadWallFourScalar68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) l := by
  have lower (p : k[X]) (hp : p.natDegree < 8 * n) :
      p.coeff (8 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA4 : (A ^ 4).coeff (8 * n) = A.coeff (2 * n) ^ 4 := by
    have h := coeff_pow_at_bound68 A (2 * n) 4 hA
    have hi : 4 * (2 * n) = 8 * n := by omega
    simpa only [hi] using h
  have hABC : (A * B * c).coeff (8 * n) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n)
      (3 * n - g) (4 * n - g) hA hB hc
    have hi : 2 * n + (3 * n - g) + (4 * n - g) = 8 * n := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (8 * n) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
    have hi : (3 * n - g) + (6 * n - g) = 8 * n := by omega
    simpa only [hi] using h
  have hDc : (D * c).coeff (8 * n) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hi : (5 * n - g) + (4 * n - g) = 8 * n := by omega
    simpa only [hi] using h
  have hB3 : (B ^ 3).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAz : A.coeff (8 * n) = 0 := lower _ (by omega)
  have hBz : B.coeff (8 * n) = 0 := lower _ (by omega)
  have hA2 : (A ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hcz : c.coeff (8 * n) = 0 := lower _ (by omega)
  have hDz : D.coeff (8 * n) = 0 := lower _ (by omega)
  have hAB : (A * B).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hez : e.coeff (8 * n) = 0 := lower _ (by omega)
  have hAc : (A * c).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hB2 : (B ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA3 : (A ^ 3).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2c : (A ^ 2 * c).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAB2 : (A * B ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAe : (A * e).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBD : (B * D).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hc2 : (c ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralFourPolynomial68, coeff_add, coeff_sub,
    coeff_smul, hABC, hBe, hDc, hB3, hAz, hBz, hA2, hcz, hDz,
    hAB, hez, hAc, hB2, hA3, hA4, hA2c, hAB2, hAe, hBD, hc2,
    smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstLoadWallFourScalar68]
  ring

end FirstLoadWallExtraction68
end Max11DegreeRoutes
