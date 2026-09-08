import LowScale68SecondaryResidualLoadZeroEndgamePart09Scratch

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

theorem polynomialSecondaryResidualBetweenFace68_classify_of_l_eq_zero
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hcn : c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨
      e.coeff (6 * n - h) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    d.coeff (5 * n - h) ≠ 0 ∧ e.coeff (6 * n - h) ≠ 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
        3 * c.coeff (4 * n - g) ^ 2 = 0 :=
  secondaryResidualBetweenFace68_classify
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hb hcn hattained
    (polynomialSecondaryResidualBetweenFace68_of_l_eq_zero
      beta gamma delta epsilon zeta i4 i3 A B c d e n g h
      hg hgh hh hsmall hA hB hc hd he hi4 hi3)

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
