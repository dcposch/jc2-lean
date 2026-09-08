import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryPairZeroScratch

/-! # First independent ordinary row at offset 180

The leading ordinary row-zero jet is I4-dependent.  In the contracted
`(4,0,2,1,3)` chart, coefficient `7` is the first independent row-zero
coefficient (expanded index `479`).  Its literal load is retained exactly.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryRowZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Homogeneous coefficient `7`, after the already-used I4 coefficients
`3` and `2` have killed the two high coefficients of `B*e+c*d`. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hsecond : B.coeff 0 * e.coeff 2 +
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 7 =
      (4 / 27 : k) *
        (-4 * A.coeff 4 ^ 2 *
            (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) -
          7 * A.coeff 4 * A.coeff 3 *
            (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
              c.coeff 0 * d.coeff 1) +
          4 * A.coeff 4 * B.coeff 0 * c.coeff 2 ^ 2 -
          12 * A.coeff 4 * d.coeff 1 * e.coeff 3) := by
  let F : k[X] := B * e + c * d
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hF : F.natDegree ≤ 3 := by simp only [F]; compute_degree; omega
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have he4 : e.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hBe3 : (B * e).coeff 3 = B.coeff 0 * e.coeff 3 := by
    rw [hBC]
    simp
  have hcd3 := coeff_mul_at_bounds68 c d 2 1 hc hd
  norm_num at hcd3
  have hF3 : F.coeff 3 = 0 := by
    simp only [F, coeff_add, hBe3, hcd3]
    linear_combination hface
  have hBe2 : (B * e).coeff 2 = B.coeff 0 * e.coeff 2 := by
    rw [hBC]
    simp
  have hcd2 : (c * d).coeff 2 =
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 := by
    rw [mul_coeff_two68, hd2]
    ring
  have hF2 : F.coeff 2 = 0 := by
    simp only [F, coeff_add, hBe2, hcd2]
    linear_combination hsecond
  have hFdeg : F.natDegree ≤ 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      by_cases hn2 : n = 2
      · simpa only [hn2] using hF2
      by_cases hn3 : n = 3
      · simpa only [hn3] using hF3
      · exact coeff_eq_zero_of_natDegree_lt
          (hF.trans_lt (by omega)))
  have hF0 : F.coeff 0 =
      B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0 := by
    simp only [F, coeff_add, mul_coeff_zero]
  have hF1 : F.coeff 1 =
      B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
        c.coeff 0 * d.coeff 1 := by
    simp only [F, coeff_add, mul_coeff_one]
    have hB1 : B.coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
    rw [hB1]
    ring
  have hAAF := coeff_mul_mul_at_reflect_one68 A (derivative A) F
    4 3 1 hA hderA hFdeg (by norm_num)
  norm_num [coeff_reflect, coeff_derivative, hF0, hF1] at hAAF
  have hAAF' : (A * derivative A * F).coeff 7 =
      4 * A.coeff 4 ^ 2 *
          (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
        7 * A.coeff 4 * A.coeff 3 *
          (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
            c.coeff 0 * d.coeff 1) := by
    linear_combination hAAF
  have h5 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    0 2 2 4 (by norm_num) hB hc hc hA
  norm_num at h5
  have h5' : (derivative A * B * c ^ 2).coeff 7 =
      4 * A.coeff 4 * B.coeff 0 * c.coeff 2 ^ 2 := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 d e A
    1 3 4 (by norm_num) hd he hA
  norm_num at h6
  have h6' : (derivative A * d * e).coeff 7 =
      4 * A.coeff 4 * d.coeff 1 * e.coeff 3 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 7 := by
    compute_degree
    omega
  have hlow4 : (A * B * derivative B * d).natDegree < 7 := by
    compute_degree
    omega
  have hlow7 : (B * c * derivative e).natDegree < 7 := by
    compute_degree
    omega
  have hlow8 : (B * d * derivative d).natDegree < 7 := by
    compute_degree
    omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 7 := by
    compute_degree
    omega
  have hlow10 : (c * derivative c * d).natDegree < 7 := by
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
  simp only [coeff_smul, coeff_add, coeff_sub, coeff_neg, hAAF', h5', h6',
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

/-- Exact literal load at the same coefficient. -/
theorem cubicLoadRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 =
      (-4 / 9 : k) * epsilon * A.coeff 4 ^ 2 * B.coeff 0 -
        (8 / 9 : k) * gamma * A.coeff 4 ^ 2 * d.coeff 0 -
        (14 / 9 : k) * gamma * A.coeff 4 * A.coeff 3 * d.coeff 1 := by
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
  have hlow1 : (B * derivative A * c).natDegree < 7 := by
    compute_degree
    omega
  have hlow2 : (B * derivative e).natDegree < 7 := by
    compute_degree
    omega
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B (1 : k[X]) A
    4 0 0 4 (by norm_num) hA hB (by norm_num) hA
  norm_num [coeff_one] at h3
  have h3' : (A * B * derivative A).coeff 7 =
      4 * A.coeff 4 ^ 2 * B.coeff 0 := by
    linear_combination h3
  have h4 := coeff_mul_mul_at_reflect_one68 A (derivative A) d
    4 3 1 hA hderA hd (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h4
  have h4' : (A * derivative A * d).coeff 7 =
      4 * A.coeff 4 ^ 2 * d.coeff 0 +
        7 * A.coeff 4 * A.coeff 3 * d.coeff 1 := by
    linear_combination h4
  have hlow5 : (d * derivative c).natDegree < 7 := by
    compute_degree
    omega
  have hlow6 : (d * derivative A).natDegree < 7 := by
    compute_degree
    omega
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 7 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, h3', h4',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6]
  ring

/-- The first independent row fixes the exact I4 residual; all gamma and
epsilon terms cancel without a nonzero assumption on either load. -/
theorem fiveToSix_ordinaryOneEighty_rowZero_i4_residual68
    (a a₃ b c x y d₀ e₀ e₁ c₀ c₁ gamma epsilon i4 : k)
    (ha : a ≠ 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hfirst : (8 / 3 : k) *
        (b * e₁ + c₁ * d₀ + c₀ * x) + 4 * gamma * x = 0)
    (hconstant : (-8 / 27 : k) * b ^ 3 +
        (8 / 3 : k) * (b * e₀ + c₀ * d₀) +
        2 * epsilon * b + 4 * gamma * d₀ = i4)
    (hrow : (4 / 27 : k) *
          (-4 * a ^ 2 * (b * e₀ + c₀ * d₀) -
            7 * a * a₃ * (b * e₁ + c₁ * d₀ + c₀ * x) +
            4 * a * b * c ^ 2 - 12 * a * x * y) -
        (4 / 9 : k) * epsilon * a ^ 2 * b -
        (8 / 9 : k) * gamma * a ^ 2 * d₀ -
        (14 / 9 : k) * gamma * a * a₃ * x = 0) :
    27 * a * i4 + 32 * a * b ^ 3 + 216 * x * y = 0 := by
  have hscaled : (-2 / 243 : k) * a *
      (27 * a * i4 + 32 * a * b ^ 3 + 216 * x * y) = 0 := by
    linear_combination hrow + (7 / 18 : k) * a * a₃ * hfirst +
      (2 / 9 : k) * a ^ 2 * hconstant -
      (16 / 81 : k) * a * b * hdisc
  exact (mul_eq_zero.mp hscaled).resolve_left
    (mul_ne_zero (by norm_num) ha)

set_option maxHeartbeats 15000000 in
/-- Source-facing contracted offset-`180` packet.  The original offset-120
nonzero-discriminant sibling is not consumed here. -/
theorem fiveToSix_offsetOneEighty_nonzero_rowZero_source_packet68
    (alpha gamma epsilon eta i4 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 1 ≠ 0) (hy : e.coeff 3 ≠ 0)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 = 0) :
    27 * A.coeff 4 * i4 + 32 * A.coeff 4 * B.coeff 0 ^ 3 +
      216 * d.coeff 1 * e.coeff 3 = 0 := by
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hBcubeDeg : (B ^ 3).natDegree ≤ 0 := by compute_degree; omega
  have hBcube2 : (B ^ 3).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
  have hBcube1 : (B ^ 3).coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
  have hBcube0 : (B ^ 3).coeff 0 = B.coeff 0 ^ 3 := by
    simp only [pow_succ, mul_coeff_zero]
    norm_num [coeff_one]
  have hcoeff2 := congrArg (fun p : k[X] => p.coeff 2) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
    at hcoeff2
  norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, mul_coeff_two68, hB1, hB2, hd2,
    hBcube2, coeff_C] at hcoeff2
  have hsecond : B.coeff 0 * e.coeff 2 +
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 = 0 := by
    linear_combination (3 / 8 : k) * hcoeff2
  have hcoeff1 := congrArg (fun p : k[X] => p.coeff 1) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
    at hcoeff1
  norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, mul_coeff_one, hB1, hBcube1, coeff_C] at hcoeff1
  have hfirst : (8 / 3 : k) *
      (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
        c.coeff 0 * d.coeff 1) + 4 * gamma * d.coeff 1 = 0 := by
    linear_combination hcoeff1
  have hcoeff0 := congrArg (fun p : k[X] => p.coeff 0) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
    at hcoeff0
  norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, mul_coeff_zero, hBcube0, coeff_C] at hcoeff0
  have hconstant : (-8 / 27 : k) * B.coeff 0 ^ 3 +
      (8 / 3 : k) *
        (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
      2 * epsilon * B.coeff 0 + 4 * gamma * d.coeff 0 = i4 := by
    linear_combination hcoeff0
  have hres :=
    secondaryResidualRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
      A B c d e hA hB hc hd he hface hsecond
  have hload := cubicLoadRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
    alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [coeff_add, hres, hload] at hrow
  exact fiveToSix_ordinaryOneEighty_rowZero_i4_residual68
    (A.coeff 4) (A.coeff 3) (B.coeff 0) (c.coeff 2)
    (d.coeff 1) (e.coeff 3) (d.coeff 0) (e.coeff 0)
    (e.coeff 1) (c.coeff 0) (c.coeff 1) gamma epsilon i4
    ha hdisc hfirst hconstant (by linear_combination hrow)

#print axioms secondaryResidualRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
#print axioms cubicLoadRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
#print axioms fiveToSix_ordinaryOneEighty_rowZero_i4_residual68
#print axioms fiveToSix_offsetOneEighty_nonzero_rowZero_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryRowZero68

end Max11DegreeRoutes
