import LowScale68SecondaryResidualDoubleLoadWallPart08Scratch

/-! # Mixed residual double face on the `(6,8)` wall `n = 3g`, `h = 2g`

On `n = 3g` the residual double face `9n-3g` collides with the Jacobian
load `l A^4` at degree `8n`.  Row two and row zero likewise meet the cores
`l A^5` and `l A^6` at `10n-1` and `12n-1`.  I3 and row one remain
load-free.  The five leading scalars force `l = b = c = 0`; residual
support `b ≠ 0 ∨ c ≠ 0` therefore excludes the wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Abstract mixed numerators -/

/-! ## Scalar identities -/

/-! ## Wall index arithmetic -/

/-! ## I4 load core versus remainder -/

/-! ## Term-by-term remainder degree bounds on `3g = n`

Cores, rest polynomials, Jacobian splits, and
`cubicLoadRowTwo/ZeroPolynomial68_eq_lCore_add_rest` are the tracked
definitions in `LowScale68SecondaryFirstLoadWallRemainder`.  Only the
wall-specific degree comparisons `3g = n` are restated here. -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_residualDoubleLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (12 * n - 1) =
      (35 / 1944 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  rw [cubicLoadRowZeroPolynomial68_eq_lCore_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroRestPolynomial68_degree_lt_wall
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hwall hA hB hc hD he), add_zero]
  exact cubicLoadRowZeroLCorePolynomial68_coeff_loadWall l A n hn hA

end Max11DegreeRoutes
