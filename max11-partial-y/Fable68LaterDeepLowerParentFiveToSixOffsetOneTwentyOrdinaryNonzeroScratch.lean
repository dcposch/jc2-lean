import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyScratch

/-! # Eliminating the ordinary offset-120 nonzero-discriminant branch

The ordinary `(n,g)=(120,360)` wall packet leaves one live alternative
with `b,c₂,d₂,e₄` all nonzero and `a*b^2+3*c₂^2=0` (contracted chart
`(4,0,2,2,4)`, edge pair at expanded offset `120`).  The wall already
consumed row-zero coefficient `11` (expanded `719`) and the two leading
first-integral coefficients; row-zero coefficient `10` (expanded `659`)
is load-free and only regenerates the I4 coefficient-`3` jet, so the
first genuinely unused lower Keller coefficient is row-zero `9`
(expanded `599`).  Consumed together with the next unused I4
coefficients `3` and `2` (expanded `180` and `120`), whose literal
`gamma` load `4*gamma*d₂` is retained, the two `gamma` loads cancel
exactly and the row leaves `(-16/9)*a*d₂*e₄ = 0`.  The branch is
impossible; the pair-zero offset-`180` sibling and the aligned
second-jet lane are untouched.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryNonzero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The coefficient of order three in a product. -/
theorem mul_coeff_three_oneTwentyOrdinaryNonzero68 (p q : k[X]) :
    (p * q).coeff 3 =
      p.coeff 0 * q.coeff 3 + p.coeff 1 * q.coeff 2 +
        p.coeff 2 * q.coeff 1 + p.coeff 3 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- Homogeneous row-zero coefficient `9` in the contracted ordinary
nonzero chart.  After the two consumed I4 jets kill the coefficients `4`
and `3` of `B*e+c*d`, only the coefficient-`2` jet and the independent
edge product `d₂*e₄` survive. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_nine_ordinaryNonzeroOneTwenty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2)
    (he : e.natDegree ≤ 4)
    (hface : B.coeff 0 * e.coeff 4 + c.coeff 2 * d.coeff 2 = 0)
    (hthird : B.coeff 0 * e.coeff 3 +
      c.coeff 2 * d.coeff 1 + c.coeff 1 * d.coeff 2 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 9 =
      (4 / 27 : k) *
        (-4 * A.coeff 4 ^ 2 *
            (B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 +
              c.coeff 1 * d.coeff 1 + c.coeff 0 * d.coeff 2) -
          12 * A.coeff 4 * d.coeff 2 * e.coeff 4) := by
  let F : k[X] := B * e + c * d
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hF : F.natDegree ≤ 4 := by
    simp only [F]
    compute_degree
    omega
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hBe4 : (B * e).coeff 4 = B.coeff 0 * e.coeff 4 := by
    rw [hBC]
    simp
  have hcd4 := coeff_mul_at_bounds68 c d 2 2 hc hd
  norm_num at hcd4
  have hF4 : F.coeff 4 = 0 := by
    simp only [F, coeff_add, hBe4, hcd4]
    linear_combination hface
  have hBe3 : (B * e).coeff 3 = B.coeff 0 * e.coeff 3 := by
    rw [hBC]
    simp
  have hcd3 : (c * d).coeff 3 =
      c.coeff 2 * d.coeff 1 + c.coeff 1 * d.coeff 2 := by
    rw [mul_coeff_three_oneTwentyOrdinaryNonzero68, hd3, hc3]
    ring
  have hF3 : F.coeff 3 = 0 := by
    simp only [F, coeff_add, hBe3, hcd3]
    linear_combination hthird
  have hFdeg : F.natDegree ≤ 2 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      by_cases hn3 : n = 3
      · simpa only [hn3] using hF3
      by_cases hn4 : n = 4
      · simpa only [hn4] using hF4
      · exact coeff_eq_zero_of_natDegree_lt
          (hF.trans_lt (by omega)))
  have hBe2 : (B * e).coeff 2 = B.coeff 0 * e.coeff 2 := by
    rw [hBC]
    simp
  have hcd2 : (c * d).coeff 2 =
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 +
        c.coeff 0 * d.coeff 2 := by
    rw [mul_coeff_two68]
    ring
  have hF2 : F.coeff 2 =
      B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 +
        c.coeff 1 * d.coeff 1 + c.coeff 0 * d.coeff 2 := by
    simp only [F, coeff_add, hBe2, hcd2]
    ring
  have hAAF := coeff_mul_mul_at_bounds68 A (derivative A) F
    4 3 2 hA hderA hFdeg
  norm_num [coeff_derivative] at hAAF
  rw [hF2] at hAAF
  have hAAF' : (A * derivative A * F).coeff 9 =
      4 * A.coeff 4 ^ 2 *
        (B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 +
          c.coeff 1 * d.coeff 1 + c.coeff 0 * d.coeff 2) := by
    linear_combination hAAF
  have h6 := coeff_mul_mul_derivative_at_bounds68 d e A
    2 4 4 (by norm_num) hd he hA
  norm_num at h6
  have h6' : (derivative A * d * e).coeff 9 =
      4 * A.coeff 4 * d.coeff 2 * e.coeff 4 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 9 := by
    compute_degree
    omega
  have hlow4 : (A * B * derivative B * d).natDegree < 9 := by
    compute_degree
    omega
  have hlow5 : (derivative A * B * c ^ 2).natDegree < 9 := by
    compute_degree
    omega
  have hlow7 : (B * c * derivative e).natDegree < 9 := by
    compute_degree
    omega
  have hlow8 : (B * d * derivative d).natDegree < 9 := by
    compute_degree
    omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 9 := by
    compute_degree
    omega
  have hlow10 : (c * derivative c * d).natDegree < 9 := by
    compute_degree
    omega
  have hrowEq : secondaryResidualRowZeroPolynomial68 A B c d e =
      (4 / 27 : k) •
        (-(A * derivative A * F) - A * B ^ 2 * derivative d -
          A * B * derivative B * d + derivative A * B * c ^ 2 -
          (3 : k) • (derivative A * d * e) +
          (3 : k) • (B * c * derivative e) -
          (3 : k) • (B * d * derivative d) -
          (3 : k) • (derivative B * d ^ 2) -
          (3 : k) • (c * derivative c * d)) := by
    simp only [secondaryResidualRowZeroPolynomial68, F, neg_smul, one_smul,
      Polynomial.smul_eq_C_mul]
    ring
  rw [hrowEq]
  simp only [coeff_smul, coeff_add, coeff_sub, coeff_neg, hAAF', h6',
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

/-- Exact literal load at the same coefficient: only the `gamma` term
`-(8/9)*gamma*a^2*d₂` attains degree `9`; every `alpha` piece cancels and
the `epsilon` pieces stay strictly below. -/
theorem cubicLoadRowZeroPolynomial68_coeff_nine_ordinaryNonzeroOneTwenty68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2)
    (he : e.natDegree ≤ 4) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 9 =
      (-8 / 9 : k) * gamma * A.coeff 4 ^ 2 * d.coeff 2 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c D0 e =
      (2 / 9 * gamma : k) • (B * derivative A * c) +
        (2 / 3 * gamma : k) • (B * derivative e) -
        (1 / 9 * epsilon : k) • (A * B * derivative A) -
        (2 / 9 * gamma : k) • (A * derivative A * d) -
        (2 / 3 * gamma : k) • (d * derivative c) -
        (1 / 3 * epsilon : k) • (d * derivative A) := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, D0,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hlow1 : (B * derivative A * c).natDegree < 9 := by
    compute_degree
    omega
  have hlow2 : (B * derivative e).natDegree < 9 := by
    compute_degree
    omega
  have hlow3 : (A * B * derivative A).natDegree < 9 := by
    compute_degree
    omega
  have h4 := coeff_mul_mul_derivative_at_bounds68 A d A
    4 2 4 (by norm_num) hA hd hA
  norm_num at h4
  have h4' : (A * derivative A * d).coeff 9 =
      4 * A.coeff 4 ^ 2 * d.coeff 2 := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h4
  have hlow5 : (d * derivative c).natDegree < 9 := by
    compute_degree
    omega
  have hlow6 : (d * derivative A).natDegree < 9 := by
    compute_degree
    omega
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 9 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, h4',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6]
  ring

/-- Row-zero coefficient `9` against the I4 coefficient-`2` load: the two
`gamma` loads cancel exactly and only the nonzero edge product remains.
No stored nonzero is divided away. -/
theorem fiveToSix_ordinaryNonzero_rowZero_i4_elimination68
    (a b c₀ c₁ c₂ d₀ d₁ x y e₂ gamma : k)
    (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hsecond : (8 / 3 : k) *
        (b * e₂ + c₂ * d₀ + c₁ * d₁ + c₀ * x) + 4 * gamma * x = 0)
    (hrow : (4 / 27 : k) *
        (-4 * a ^ 2 * (b * e₂ + c₂ * d₀ + c₁ * d₁ + c₀ * x) -
          12 * a * x * y) +
        (-8 / 9 : k) * gamma * a ^ 2 * x = 0) :
    False := by
  have hscaled : (-16 / 9 : k) * (a * (x * y)) = 0 := by
    linear_combination hrow + (2 / 9 : k) * a ^ 2 * hsecond
  have hprod : a * (x * y) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left (by norm_num)
  exact (mul_ne_zero ha (mul_ne_zero hx hy)) hprod

set_option maxHeartbeats 15000000 in
/-- Source-facing contracted elimination of the ordinary offset-`120`
nonzero-discriminant branch.  The three consumed I4 coefficients `4,3,2`
(expanded `240,180,120`) supply the face, the third jet, and the loaded
second jet; row-zero coefficient `9` (expanded `599`) then forces
`a*d₂*e₄ = 0` against the retained branch nonzeros.  The pair-zero
offset-`180` sibling and the aligned second-jet packets are preserved
literally elsewhere. -/
theorem fiveToSix_offsetOneTwenty_ordinary_nonzero_source_false68
    (alpha gamma epsilon eta i4 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2)
    (he : e.natDegree ≤ 4)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 2 ≠ 0) (hy : e.coeff 4 ≠ 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 9 = 0) :
    False := by
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB3 : B.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB4 : B.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd4 : d.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hBcubeDeg : (B ^ 3).natDegree ≤ 0 := by
    compute_degree
    omega
  have hBcube2 : (B ^ 3).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
  have hBcube3 : (B ^ 3).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
  have hBcube4 : (B ^ 3).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
  have hBe4 : (B * e).coeff 4 = B.coeff 0 * e.coeff 4 := by
    rw [hBC]
    simp
  have hBe3 : (B * e).coeff 3 = B.coeff 0 * e.coeff 3 := by
    rw [hBC]
    simp
  have hBe2 : (B * e).coeff 2 = B.coeff 0 * e.coeff 2 := by
    rw [hBC]
    simp
  have hcd4 := coeff_mul_at_bounds68 c d 2 2 hc hd
  norm_num at hcd4
  have hcd3 : (c * d).coeff 3 =
      c.coeff 2 * d.coeff 1 + c.coeff 1 * d.coeff 2 := by
    rw [mul_coeff_three_oneTwentyOrdinaryNonzero68, hd3, hc3]
    ring
  have hcd2 : (c * d).coeff 2 =
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 +
        c.coeff 0 * d.coeff 2 := by
    rw [mul_coeff_two68]
    ring
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff 4) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
    at hcoeff4
  norm_num [coeff_add, coeff_smul, smul_eq_mul,
    secondaryResidualInvariantFourPolynomial68, hBcube4, hBe4, hcd4,
    hB4, hd4, coeff_C] at hcoeff4
  have hface : B.coeff 0 * e.coeff 4 + c.coeff 2 * d.coeff 2 = 0 := by
    linear_combination (3 / 8 : k) * hcoeff4
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff 3) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
    at hcoeff3
  norm_num [coeff_add, coeff_smul, smul_eq_mul,
    secondaryResidualInvariantFourPolynomial68, hBcube3, hBe3, hcd3,
    hB3, hd3, coeff_C] at hcoeff3
  have hthird : B.coeff 0 * e.coeff 3 +
      c.coeff 2 * d.coeff 1 + c.coeff 1 * d.coeff 2 = 0 := by
    linear_combination (3 / 8 : k) * hcoeff3
  have hcoeff2 := congrArg (fun p : k[X] => p.coeff 2) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
    at hcoeff2
  norm_num [coeff_add, coeff_smul, smul_eq_mul,
    secondaryResidualInvariantFourPolynomial68, hBcube2, hBe2, hcd2,
    hB2, coeff_C] at hcoeff2
  have hsecond : (8 / 3 : k) *
      (B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 +
        c.coeff 1 * d.coeff 1 + c.coeff 0 * d.coeff 2) +
      4 * gamma * d.coeff 2 = 0 := by
    linear_combination hcoeff2
  have hres :=
    secondaryResidualRowZeroPolynomial68_coeff_nine_ordinaryNonzeroOneTwenty68
      A B c d e hA hB hc hd he hface hthird
  have hload :=
    cubicLoadRowZeroPolynomial68_coeff_nine_ordinaryNonzeroOneTwenty68
      alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [coeff_add, hres, hload] at hrow
  exact fiveToSix_ordinaryNonzero_rowZero_i4_elimination68
    (A.coeff 4) (B.coeff 0) (c.coeff 0) (c.coeff 1) (c.coeff 2)
    (d.coeff 0) (d.coeff 1) (d.coeff 2) (e.coeff 4) (e.coeff 2) gamma
    ha hx hy hsecond (by linear_combination hrow)

#print axioms mul_coeff_three_oneTwentyOrdinaryNonzero68
#print axioms secondaryResidualRowZeroPolynomial68_coeff_nine_ordinaryNonzeroOneTwenty68
#print axioms cubicLoadRowZeroPolynomial68_coeff_nine_ordinaryNonzeroOneTwenty68
#print axioms fiveToSix_ordinaryNonzero_rowZero_i4_elimination68
#print axioms fiveToSix_offsetOneTwenty_ordinary_nonzero_source_false68

end LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryNonzero68

end Max11DegreeRoutes
