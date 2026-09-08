import LowScale68SecondaryResidualDoubleLoadWallPart10Scratch

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

/-! ## Homogeneous residual one-forms at the wall indices -/

set_option maxHeartbeats 2000000 in
theorem secondaryResidualRowOnePolynomial68_coeff_doubleLoadWall
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff (11 * n - 1) =
      (8 / 27 : k) *
        (3 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (g : k) *
            d.coeff (5 * n - 2 * g) -
          10 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (n : k) *
            d.coeff (5 * n - 2 * g) +
          2 * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 * (n : k) *
            c.coeff (4 * n - g) -
          9 * A.coeff (2 * n) * (g : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          30 * A.coeff (2 * n) * (n : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          3 * (g : k) * c.coeff (4 * n - g) ^ 3 -
          12 * (n : k) * c.coeff (4 * n - g) ^ 3) := by
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have hidx : 12 * n - 3 * g - 1 = 11 * n - 1 :=
    residualDoubleLoadWall_oneIndex n g hwall
  rw [← hidx, secondaryResidualRowOnePolynomial68_coeff_double_of_twoGap
    A B c d e n g hg htwo hA hB hc hd he]

set_option maxHeartbeats 2000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_doubleLoadWall
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (12 * n - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        residualDoubleZeroHom68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
          (e.coeff (6 * n - 2 * g)) := by
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have hidx : 13 * n - 3 * g - 1 = 12 * n - 1 :=
    residualDoubleLoadWall_zeroIndex n g hwall
  rw [← hidx, secondaryResidualRowZeroPolynomial68_coeff_double_of_twoGap
    A B c d e n g hg htwo hA hB hc hd he]
  simp only [residualDoubleZeroHom68]
  ring

end Max11DegreeRoutes
