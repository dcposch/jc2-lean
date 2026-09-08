import LowScale68SecondaryResidualLoadZeroEndgamePart24Scratch

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

set_option maxHeartbeats 2000000 in
/-- Vanishing of the balanced cubic-face coefficient is equivalent to
`4*b*c_top^2 - 9*d_top*e_top = 0`. -/
theorem residualRowTwo_balanced_coeff_eq_zero_iff68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 ↔
      (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  rw [residualRowTwo_coeff_balancedChamber68_of_twoGap A B c d e n g h hg hgh hh hsmall
    hbalanced hA hB hc hd he hQ hdisc]
  constructor
  · intro h
    have hsc : (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
      mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
    exact (mul_eq_zero.mp h).resolve_left hsc
  · intro h
    rw [h, mul_zero]

/-- Same conclusion if residual row two cancels a load strictly below the
cubic face. -/
theorem residualRowTwo_add_load_eq_zero_imp_balancedRelation68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff :
      (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum
    rw [coeff_add, coeff_zero,
      coeff_eq_zero_of_natDegree_lt hload, add_zero] at h
    exact h
  exact (residualRowTwo_balanced_coeff_eq_zero_iff68_of_twoGap A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hc hd he hQ hdisc).1 hcoeff

/-- Residual row two identically zero implies the balanced scalar relation. -/
theorem residualRowTwo_eq_zero_imp_balancedRelation68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff :
      (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 := by
    simp [hrow]
  exact (residualRowTwo_balanced_coeff_eq_zero_iff68_of_twoGap A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hc hd he hQ hdisc).1 hcoeff

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
