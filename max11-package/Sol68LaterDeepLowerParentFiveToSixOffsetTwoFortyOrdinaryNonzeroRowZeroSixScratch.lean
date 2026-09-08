import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroRowZeroScratch

/-! # Offset-240 nonzero row-zero coefficient 6

The first row fixed I4.  The next source coefficient, contracted row-zero
`6` (expanded index `419`), is independent and fixes the first jet of the
discriminant cusp.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroSix68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 20000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Homogeneous row-zero coefficient `6` after the face and its I4 jet
have killed coefficients `2` and `1` of `B*e+c*d`. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_six_ordinaryTwoForty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0)
    (hfirst : B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 6 =
      (4 / 27 : k) *
        (-7 * A.coeff 3 * A.coeff 4 *
            (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
          3 * A.coeff 3 * B.coeff 0 * c.coeff 2 ^ 2 +
          8 * A.coeff 4 * B.coeff 0 * c.coeff 1 * c.coeff 2) := by
  let F : k[X] := B * e + c * d
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hF : F.natDegree ≤ 2 := by simp only [F]; compute_degree; omega
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hBe2 : (B * e).coeff 2 = B.coeff 0 * e.coeff 2 := by
    rw [hBC]
    simp
  have hcd2 := coeff_mul_at_bounds68 c d 2 0 hc hd
  norm_num at hcd2
  have hF2 : F.coeff 2 = 0 := by
    simp only [F, coeff_add, hBe2, hcd2]
    linear_combination hface
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hd1 : d.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hBe1 : (B * e).coeff 1 = B.coeff 0 * e.coeff 1 := by
    rw [hBC]
    simp
  have hcd1 : (c * d).coeff 1 = c.coeff 1 * d.coeff 0 := by
    rw [mul_coeff_one, hd1]
    ring
  have hF1 : F.coeff 1 = 0 := by
    simp only [F, coeff_add, hBe1, hcd1]
    linear_combination hfirst
  have hFdeg : F.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      by_cases hn1 : n = 1
      · simpa only [hn1] using hF1
      by_cases hn2 : n = 2
      · simpa only [hn2] using hF2
      · exact coeff_eq_zero_of_natDegree_lt (hF.trans_lt (by omega)))
  have hF0 : F.coeff 0 =
      B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0 := by
    simp only [F, coeff_add, mul_coeff_zero]
  have hAAF := coeff_mul_mul_at_reflect_one68 A (derivative A) F
    4 3 0 hA hderA hFdeg (by norm_num)
  norm_num [coeff_reflect, coeff_derivative, hF0] at hAAF
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hF1] at hAAF
  simp only [mul_zero, add_zero] at hAAF
  have hAAF' : (A * derivative A * F).coeff 6 =
      7 * A.coeff 3 * A.coeff 4 *
        (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) := by
    linear_combination hAAF
  have h5 := coeff_mul_mul_mul_at_reflect_one68
    (derivative A) B c c 3 0 2 2 hderA hB hc hc (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h5
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hB1] at h5
  simp only [mul_zero, zero_mul, add_zero] at h5
  have h5' : (derivative A * B * c ^ 2).coeff 6 =
      3 * A.coeff 3 * B.coeff 0 * c.coeff 2 ^ 2 +
        8 * A.coeff 4 * B.coeff 0 * c.coeff 1 * c.coeff 2 := by
    rw [pow_two]
    calc
      (derivative A * B * (c * c)).coeff 6 =
          (derivative A * B * c * c).coeff 6 := by
            congr 1
            ring
      _ = _ := by rw [h5]; ring
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 6 := by
    compute_degree; omega
  have hlow4 : (A * B * derivative B * d).natDegree < 6 := by
    compute_degree; omega
  have hlow6 : (derivative A * d * e).natDegree < 6 := by
    compute_degree; omega
  have hlow7 : (B * c * derivative e).natDegree < 6 := by
    compute_degree; omega
  have hlow8 : (B * d * derivative d).natDegree < 6 := by
    compute_degree; omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 6 := by
    compute_degree; omega
  have hlow10 : (c * derivative c * d).natDegree < 6 := by
    compute_degree; omega
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
  simp only [coeff_smul, coeff_add, coeff_sub, coeff_neg, hAAF', h5',
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

/-- Literal load at row-zero coefficient `6`. -/
theorem cubicLoadRowZeroPolynomial68_coeff_six_ordinaryTwoForty68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 =
      (-7 / 9 : k) * epsilon * A.coeff 3 * A.coeff 4 * B.coeff 0 -
        (14 / 9 : k) * gamma * A.coeff 3 * A.coeff 4 * d.coeff 0 := by
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
      cubicLoadVPolynomial68, D0, zero_mul, zero_smul, smul_zero, add_zero,
      zero_add, sub_zero, derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_smul, derivative_C, one_mul,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
      map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast,
      map_one]
    ring
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hlow1 : (B * derivative A * c).natDegree < 6 := by
    compute_degree; omega
  have hlow2 : (B * derivative e).natDegree < 6 := by
    compute_degree; omega
  have h3 := coeff_mul_mul_at_reflect_one68 A B (derivative A)
    4 0 3 hA hB hderA (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h3
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1)] at h3
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  rw [hB1] at h3
  simp only [mul_zero, add_zero] at h3
  have h3' : (A * B * derivative A).coeff 6 =
      7 * A.coeff 3 * A.coeff 4 * B.coeff 0 := by
    linear_combination h3
  have h4 := coeff_mul_mul_at_reflect_one68 A (derivative A) d
    4 3 0 hA hderA hd (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h4
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1)] at h4
  have hd1 : d.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  rw [hd1] at h4
  simp only [mul_zero, add_zero] at h4
  have h4' : (A * derivative A * d).coeff 6 =
      7 * A.coeff 3 * A.coeff 4 * d.coeff 0 := by
    linear_combination h4
  have hlow5 : (d * derivative c).natDegree < 6 := by
    compute_degree; omega
  have hlow6 : (d * derivative A).natDegree < 6 := by
    compute_degree; omega
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 6 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, h3', h4',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6]
  ring

/-- The rigid I4 scalar cancels the coefficient-`6` constant load and
leaves exactly the first discriminant jet. -/
theorem fiveToSix_ordinaryTwoForty_rowZero_six_jet68
    (a a3 b c c0 c1 d e gamma epsilon i4 : k)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hrigid : 27 * a * i4 + 32 * a * b ^ 3 = 0)
    (hconstant : (-8 / 27 : k) * b ^ 3 +
        (8 / 3 : k) * (b * e + c0 * d) +
        2 * epsilon * b + 4 * gamma * d = i4)
    (hrow : (4 / 27 : k) *
          (-7 * a3 * a * (b * e + c0 * d) +
            3 * a3 * b * c ^ 2 + 8 * a * b * c1 * c) -
        (7 / 9 : k) * epsilon * a3 * a * b -
        (14 / 9 : k) * gamma * a3 * a * d = 0) :
    a3 * c - 2 * a * c1 = 0 := by
  have hconstantWall :
      4 * a * (b * e + c0 * d) + 3 * a * epsilon * b +
          6 * a * gamma * d - 4 * b * c ^ 2 = 0 := by
    linear_combination (1 / 18 : k) * hrigid +
      (3 / 2 : k) * a * hconstant - (4 / 3 : k) * b * hdisc
  have hprod : (16 / 27 : k) * b * c *
      (2 * a * c1 - a3 * c) = 0 := by
    linear_combination hrow + (7 / 27 : k) * a3 * hconstantWall
  have hbc : (16 / 27 : k) * b * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hb) hc
  have hz := (mul_eq_zero.mp hprod).resolve_left hbc
  linear_combination -hz

set_option maxHeartbeats 12000000 in
/-- Exact source-facing coefficient-`6` successor. -/
theorem fiveToSix_offsetTwoForty_nonzero_rowZero_six_source_packet68
    (alpha gamma epsilon eta i4 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 0 ≠ 0) (hy : e.coeff 2 ≠ 0)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hrigid : 27 * A.coeff 4 * i4 +
      32 * A.coeff 4 * B.coeff 0 ^ 3 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 = 0) :
    (27 * A.coeff 4 * i4 + 32 * A.coeff 4 * B.coeff 0 ^ 3 = 0) ∧
      A.coeff 3 * c.coeff 2 - 2 * A.coeff 4 * c.coeff 1 = 0 := by
  have hd1 : d.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hBcubeDeg : (B ^ 3).natDegree ≤ 0 := by compute_degree; omega
  have hBcube1 : (B ^ 3).coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
  have hBcube0 : (B ^ 3).coeff 0 = B.coeff 0 ^ 3 := by
    simp only [pow_succ, mul_coeff_zero]
    norm_num [coeff_one]
  have hcoeff1 := congrArg (fun p : k[X] => p.coeff 1) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
      at hcoeff1
  norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, mul_coeff_one, hB1, hd1, hBcube1,
    coeff_C] at hcoeff1
  have hfirst : B.coeff 0 * e.coeff 1 +
      c.coeff 1 * d.coeff 0 = 0 := by
    have hscale : (8 / 3 : k) *
        (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0) = 0 := by
      linear_combination hcoeff1
    exact (mul_eq_zero.mp hscale).resolve_left (by norm_num)
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
  have hres := secondaryResidualRowZeroPolynomial68_coeff_six_ordinaryTwoForty68
    A B c d e hA hB hc hd he hface hfirst
  have hload := cubicLoadRowZeroPolynomial68_coeff_six_ordinaryTwoForty68
    alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [coeff_add, hres, hload] at hrow
  refine ⟨hrigid, ?_⟩
  exact fiveToSix_ordinaryTwoForty_rowZero_six_jet68
    (A.coeff 4) (A.coeff 3) (B.coeff 0) (c.coeff 2)
    (c.coeff 0) (c.coeff 1) (d.coeff 0) (e.coeff 0) gamma epsilon i4
    hb hcTop hdisc hrigid hconstant (by linear_combination hrow)

#print axioms secondaryResidualRowZeroPolynomial68_coeff_six_ordinaryTwoForty68
#print axioms cubicLoadRowZeroPolynomial68_coeff_six_ordinaryTwoForty68
#print axioms fiveToSix_ordinaryTwoForty_rowZero_six_jet68
#print axioms fiveToSix_offsetTwoForty_nonzero_rowZero_six_source_packet68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroSix68

end Max11DegreeRoutes
