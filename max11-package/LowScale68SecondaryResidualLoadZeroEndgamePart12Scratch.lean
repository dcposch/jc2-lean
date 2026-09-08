import LowScale68SecondaryResidualLoadZeroEndgamePart11Scratch

/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

set_option maxHeartbeats 3000000 in
/-- Coefficient of the residual terminal one-form on the double face. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_double_of_twoGap
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g)) -
          A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow3 : (derivative A * d * e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  push_cast
  ring

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
