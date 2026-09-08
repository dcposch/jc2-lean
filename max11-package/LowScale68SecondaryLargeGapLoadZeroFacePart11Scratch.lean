import LowScale68SecondaryLargeGapLoadZeroFacePart10Scratch

/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on `g < n` -/

/-! ## Homogeneous residual middle coefficients -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c D e n g h hg hlarge hg_lt hh
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_largeGapLoadZero
      B c d e n g h hg hgh hh hlarge hg_lt hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c D e n g h hg hlarge hg_lt hh
      hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_middle_of_largeGapLoadZero
      A B c d e n g h hg hgh hh hlarge hg_lt hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
