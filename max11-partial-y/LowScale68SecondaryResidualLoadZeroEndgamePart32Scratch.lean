import LowScale68SecondaryResidualLoadZeroEndgamePart31Scratch

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

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

/-- Residual data on the balanced wall after `l=0`, with chamber `2g<n`. -/
structure LoadZeroBalancedResidualData68
    (A B c d e : k[X]) (n g h : ℕ) : Prop where
  hg : 0 < g
  hgh : g < h
  hh : h < 2 * g
  hsmall : 2 * g < n
  hbalanced : 2 * h = 3 * g
  hA : A.natDegree ≤ 2 * n
  hB : B.natDegree ≤ 3 * n - g
  hcdeg : c.natDegree ≤ 4 * n - g
  hd : d.natDegree ≤ 5 * n - h
  he : e.natDegree ≤ 6 * n - h
  ha0 : A.coeff (2 * n) ≠ 0
  hb0 : B.coeff (3 * n - g) ≠ 0
  hc0 : c.coeff (4 * n - g) ≠ 0
  hd0 : d.coeff (5 * n - h) ≠ 0
  he0 : e.coeff (6 * n - h) ≠ 0
  hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
    (3 : k) * c.coeff (4 * n - g) ^ 2 = 0
  hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
    c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0
  hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
    (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0
  hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
    10 * n - 3 * g

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
