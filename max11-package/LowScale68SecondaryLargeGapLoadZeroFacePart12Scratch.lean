import LowScale68SecondaryLargeGapLoadZeroFacePart11Scratch

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

theorem polynomialSecondaryResidualBetweenFace68_of_largeGapLoadZero
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hlarge hg_lt hA hB hc hd he] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hlarge hg_lt hA hB hc hd he] at hz
    have hindex : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_double_of_largeGapLoadZero
    (B c d e : k[X]) (n g : ℕ) (hg : 0 < g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hB3i] at hB3
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - 2 * g) hB he
  have hBei : (3 * n - g) + (6 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - 2 * g) hc hd
  have hcdi : (4 * n - g) + (5 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3, hBe, hcd]
  ring

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
