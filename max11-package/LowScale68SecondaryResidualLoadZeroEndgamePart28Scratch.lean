import LowScale68SecondaryResidualLoadZeroEndgamePart27Scratch

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

theorem residualRowOne_add_load_eq_zero_imp_false68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)
    (hload : load.natDegree < 12 * n - 3 * g - 1)
    (hsum : secondaryResidualRowOnePolynomial68 A B c d e + load = 0) :
    False := by
  have hcoeff :
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hsum
    rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload,
      add_zero] at h
    exact h
  exact residualRowOne_balanced_coeff_ne_zero68_of_twoGap A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

theorem residualRowOne_eq_zero_imp_false68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e = 0) :
    False := by
  have hcoeff :
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0 := by
    simp [hrow]
  exact residualRowOne_balanced_coeff_ne_zero68_of_twoGap A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_leftChamber68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    False := by
  have hidx : 11 * n - 3 * g - 1 < 11 * n - 2 * h - 1 := by omega
  have hload' : load.natDegree < 11 * n - 2 * h - 1 := hload.trans hidx
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e load (11 * n - 2 * h - 1) hload' hsum
  exact residualRowTwo_leftChamber_ne_zero68_of_twoGap A B c d e n g h
    hg hgh hh hsmall hleft hA hB hc hd he hQ hd0 he0 hcoeff0

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
