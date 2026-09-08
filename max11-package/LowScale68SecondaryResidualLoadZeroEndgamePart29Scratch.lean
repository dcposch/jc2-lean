import LowScale68SecondaryResidualLoadZeroEndgamePart28Scratch

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

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_rightChamber68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0) :
    False := by
  have ha0 := residualDisc_imp_leadingA_ne_zero68
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    hdisc hc0
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e load (11 * n - 3 * g - 1) hload hsum
  exact residualRowTwo_rightChamber_ne_zero68_of_twoGap A B c d e n g h
    hg hgh hh hsmall hright hA hB hc hd he hQ hdisc ha0 hb0 hcoeff0

set_option maxHeartbeats 2000000 in
theorem residualSelectedGap_eq_balanced68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    2 * h = 3 * g := by
  rcases lt_trichotomy (2 * h) (3 * g) with hleft | heq | hright
  · exact (residualRowTwo_not_leftChamber68_of_twoGap A B c d e load n g h
      hg hgh hh hsmall hleft hA hB hc hd he hQ hload hsum hd0 he0).elim
  · exact heq
  · exact (residualRowTwo_not_rightChamber68_of_twoGap A B c d e load n g h
      hg hgh hh hsmall hright hA hB hc hd he hQ hload hsum hdisc hb0 hc0).elim

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
