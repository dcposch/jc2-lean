import LowScale68SecondaryFirstLoadWallCorePart02Scratch

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
/-- I3 is unchanged on this wall: the `l A^3 B` load sits at `9n-g < 9n`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_loadWall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (9 * n) =
      (4 / 9 : k) * firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 9 * n) :
      p.coeff (9 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2coeff : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hA2B2 : (A ^ 2 * B ^ 2).coeff (9 * n) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_mul_at_bounds68 (A ^ 2) (B ^ 2) (4 * n)
      (6 * n - 2 * g) hA2deg hB2deg
    have hi : 4 * n + (6 * n - 2 * g) = 9 * n := by omega
    rw [hi, hA2coeff, hB2coeff] at h
    exact h
  have hABD : (A * B * D).coeff (9 * n) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B D (2 * n)
      (3 * n - g) (5 * n - g) hA hB hD
    have hi : 2 * n + (3 * n - g) + (5 * n - g) = 9 * n := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (9 * n) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 9 * n := by omega
    simpa only [hi] using h
  have hce : (c * e).coeff (9 * n) =
      c.coeff (4 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
    have hi : (4 * n - g) + (6 * n - g) = 9 * n := by omega
    simpa only [hi] using h
  have hB2c : (B ^ 2 * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBz : B.coeff (9 * n) = 0 := lower _ (by omega)
  have hcz : c.coeff (9 * n) = 0 := lower _ (by omega)
  have hez : e.coeff (9 * n) = 0 := lower _ (by omega)
  have hB2z : (B ^ 2).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hDz : D.coeff (9 * n) = 0 := lower _ (by omega)
  have hAB : (A * B).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2B : (A ^ 2 * B).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAD : (A * D).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBc : (B * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA3B : (A ^ 3 * B).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2D : (A ^ 2 * D).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hABc : (A * B * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hB3 : (B ^ 3).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBe : (B * e).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hDc : (D * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralThreePolynomial68, coeff_add, coeff_sub,
    coeff_smul, hA2B2, hABD, hB2c, hD2, hce, hBz, hcz, hez, hB2z,
    hDz, hAB, hA2B, hAD, hBc, hA3B, hA2D, hABc, hB3, hBe, hDc,
    smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryThree68]
  ring

/-! ### Homogeneous one-form cores at the wall indices -/

end FirstLoadWallExtraction68
end Max11DegreeRoutes
