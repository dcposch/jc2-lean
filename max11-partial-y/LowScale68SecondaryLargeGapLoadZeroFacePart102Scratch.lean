import LowScale68SecondaryLargeGapLoadZeroFacePart101Scratch

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

private theorem leaf68_natDegree_mulDeriv_lt {p q : k[X]} {u v bound : ℕ}
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) (h : u + (v - 1) < bound) :
    (p * derivative q).natDegree < bound :=
  natDegree_mul_le.trans_lt
    (lt_of_le_of_lt
      (Nat.add_le_add hp ((natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1))) h)

private theorem leaf68_natDegree_smul_lt (r : k) {p : k[X]} {bound : ℕ}
    (h : p.natDegree < bound) : (r • p).natDegree < bound :=
  (natDegree_smul_le r p).trans_lt h

private theorem leaf68_natDegree_add_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p + q).natDegree < bound :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem leaf68_natDegree_sub_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p - q).natDegree < bound :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)


/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on `g < n` -/

set_option maxHeartbeats 3000000 in
/-- After `l=0` the heaviest row-one load sits at `10n-1`, strictly below
the cubic residual index `12n-3g-1` once `3g < 2n`. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_largeGapLoadZero
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hrow : 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        12 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_largeGap
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hlarge hg_lt hA hB hc hD he'
  have hTl : Tl.natDegree ≤ 4 * n := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlD : (Ul * derivative D).natDegree < 12 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hUl hD (by omega)
  have hTlE : (Tl * derivative E).natDegree < 12 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hTl hE (by omega)
  have hC0Vl : (C0 * derivative Vl).natDegree < 12 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hC0 hVl (by omega)
  have hDUl : (D * derivative Ul).natDegree < 12 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hD hUl (by omega)
  change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
  exact leaf68_natDegree_sub_lt
        (leaf68_natDegree_sub_lt
          (leaf68_natDegree_add_lt
            hUlD
            (leaf68_natDegree_smul_lt (2 : k)
              hTlE))
          (leaf68_natDegree_smul_lt (2 : k)
            hC0Vl))
        hDUl

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_largeGapLoadZero
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 3 * g - 1 := by
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_largeGap
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    (by omega) hg hlarge hg_lt hA hB hc hD he'
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlE : (Ul * derivative E).natDegree <
      13 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hUl hE (by omega)
  have hDVl : (D * derivative Vl).natDegree <
      13 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hD hVl (by omega)
  change (Ul * derivative E - D * derivative Vl).natDegree < _
  exact leaf68_natDegree_sub_lt
        hUlE
        hDVl

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
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
theorem secondaryResidualInvariantFourPolynomial68_coeff_middle_of_largeGapLoadZero
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_middle_of_largeGapLoadZero
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) =
      10 * n - g - h := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 10 * n - g - h := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual double invariants -/

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_double_of_largeGapLoadZero
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - 2 * g) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c (3 * n - g)
    (3 * n - g) (4 * n - g) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g) =
      10 * n - 3 * g := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g) + (6 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c D e n g hg hlarge hg_lt
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_double_of_largeGapLoadZero
      B c d e n g hg hlarge hg_lt hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual double invariants -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c D e n g hg hlarge hg_lt
      hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_double_of_largeGapLoadZero
      A B c d e n g hg hlarge hg_lt hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

theorem polynomialSecondaryResidualDoubleInvariants68_of_largeGapLoadZero
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    -(B.coeff (3 * n - g) ^ 3) +
        9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
        9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0 ∧
      -(A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c d e n g hg hlarge hg_lt
      hA hB hc hd he] at hz
    have hindex : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_largeGapLoadZero
      beta gamma delta epsilon zeta A B c d e n g hg hlarge hg_lt
      hA hB hc hd he] at hz
    have hindex : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual double invariants -/

/-! ## Canonical residual faces -/

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, after `l = 0` on `n < 2g` and
`g < n`, every residual middle window `g < h < 2g` supplies the ordinary
two invariant equations. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualMiddleFace68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (h : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g)
    (hgap :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < n)
    (hgh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < h)
    (hh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      h < 2 * g)
    (hmiddle :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    l = 0 ∧
      SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (ee.coeff (6 * n - h)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change n < 2 * g at hlarge
  change g < n at hgap
  change g < h at hgh
  change h < 2 * g at hh
  change d.natDegree ≤ 5 * n - h ∧
    ee.natDegree ≤ 6 * n - h at hmiddle
  change l = 0 ∧
    SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h))
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hl : l = 0 := hclass.1
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  exact ⟨hl,
    polynomialSecondaryResidualBetweenFace68_of_largeGapLoadZero
      beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h
      hg hgh hh hlarge hgap hA hB hc hmiddle.1 hmiddle.2 hi4c hi3c⟩

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual double invariants -/

/-! ## Canonical residual faces -/

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, after `l = 0` on `n < 2g` and
`g < n`, every residual double window `h ≥ 2g` (including vanishing
residuals) supplies the ordinary tied-double I4/I3 pair. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualDoubleInvariants68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g)
    (hgap :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < n)
    (hdouble :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ 5 * n - 2 * g ∧ ee.natDegree ≤ 6 * n - 2 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    l = 0 ∧
      (-(Be.coeff (3 * n - g) ^ 3) +
          9 * Be.coeff (3 * n - g) * ee.coeff (6 * n - 2 * g) +
          9 * ce.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0) ∧
      (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          Be.coeff (3 * n - g) ^ 2 * ce.coeff (4 * n - g) +
          3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - 2 * g) = 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change n < 2 * g at hlarge
  change g < n at hgap
  change d.natDegree ≤ 5 * n - 2 * g ∧
    ee.natDegree ≤ 6 * n - 2 * g at hdouble
  change l = 0 ∧
    (-(Be.coeff (3 * n - g) ^ 3) +
        9 * Be.coeff (3 * n - g) * ee.coeff (6 * n - 2 * g) +
        9 * ce.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0) ∧
    (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        Be.coeff (3 * n - g) ^ 2 * ce.coeff (4 * n - g) +
        3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - 2 * g) = 0)
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hl : l = 0 := hclass.1
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  exact ⟨hl,
    polynomialSecondaryResidualDoubleInvariants68_of_largeGapLoadZero
      beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g
      hg hlarge hgap hA hB hc hdouble.1 hdouble.2 hi4c hi3c⟩

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
