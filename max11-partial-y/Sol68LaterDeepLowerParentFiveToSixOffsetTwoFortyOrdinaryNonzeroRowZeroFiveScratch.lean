import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroRowZeroSixScratch

/-! # Offset-240 nonzero row-zero coefficient 5

Contracted row-zero coefficient `5` (expanded index `359`) retains both
epsilon and gamma loads.  After the rigid I4 scalar and first cusp jet are
substituted, it fixes the exact second cusp jet.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroFive68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 25000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem mul_coeff_five_twoForty68 (p q : k[X]) :
    (p * q).coeff 5 =
      p.coeff 0 * q.coeff 5 + p.coeff 1 * q.coeff 4 +
        p.coeff 2 * q.coeff 3 + p.coeff 3 * q.coeff 2 +
        p.coeff 4 * q.coeff 1 + p.coeff 5 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

theorem mul_coeff_three_twoForty68 (p q : k[X]) :
    (p * q).coeff 3 =
      p.coeff 0 * q.coeff 3 + p.coeff 1 * q.coeff 2 +
        p.coeff 2 * q.coeff 1 + p.coeff 3 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

theorem mul_derivative_coeff_five_twoForty68
    (A : k[X]) (hA : A.natDegree ≤ 4) :
    (A * derivative A).coeff 5 =
      6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2 := by
  have hA5 : A.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have hA6 : A.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have h := mul_coeff_five_twoForty68 A (derivative A)
  norm_num [coeff_derivative, hA5, hA6] at h
  linear_combination h

theorem secondaryResidualRowZeroPolynomial68_coeff_five_ordinaryTwoForty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0)
    (hfirst : B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 5 =
      (4 / 27 : k) *
        (-(6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) *
            (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
          2 * A.coeff 2 * B.coeff 0 * c.coeff 2 ^ 2 +
          6 * A.coeff 3 * B.coeff 0 * c.coeff 1 * c.coeff 2 +
          8 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 2 +
          4 * A.coeff 4 * B.coeff 0 * c.coeff 1 ^ 2 -
          12 * A.coeff 4 * d.coeff 0 * e.coeff 2) := by
  let F : k[X] := B * e + c * d
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
  have hFpos : ∀ j, 0 < j → F.coeff j = 0 := by
    intro j hj
    exact coeff_eq_zero_of_natDegree_lt (hFdeg.trans_lt hj)
  have hG5 := mul_derivative_coeff_five_twoForty68 A hA
  have hAAFraw := mul_coeff_five_twoForty68 (A * derivative A) F
  rw [hFpos 1 (by norm_num), hFpos 2 (by norm_num),
    hFpos 3 (by norm_num), hFpos 4 (by norm_num),
    hFpos 5 (by norm_num), hG5, hF0] at hAAFraw
  have hAAF : (A * derivative A * F).coeff 5 =
      (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) *
        (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) := by
    linear_combination hAAFraw
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hA'Bdeg : (derivative A * B).natDegree ≤ 3 := by
    compute_degree; omega
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB3 : B.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hP1 : (derivative A * B).coeff 1 =
      2 * A.coeff 2 * B.coeff 0 := by
    have h := mul_coeff_one (derivative A) B
    rw [hB1] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hP2 : (derivative A * B).coeff 2 =
      3 * A.coeff 3 * B.coeff 0 := by
    have h := mul_coeff_two68 (derivative A) B
    rw [hB1, hB2] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hP3 : (derivative A * B).coeff 3 =
      4 * A.coeff 4 * B.coeff 0 := by
    have h := coeff_mul_at_bounds68 (derivative A) B 3 0 hderA hB
    norm_num [coeff_derivative] at h
    linear_combination h
  have hP4 : (derivative A * B).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
  have hP5 : (derivative A * B).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
  have hcsqdeg : (c ^ 2).natDegree ≤ 4 := by compute_degree; omega
  have hcsq2 : (c ^ 2).coeff 2 =
      2 * c.coeff 0 * c.coeff 2 + c.coeff 1 ^ 2 := by
    rw [pow_two, mul_coeff_two68]
    ring
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hcsq3 : (c ^ 2).coeff 3 = 2 * c.coeff 1 * c.coeff 2 := by
    rw [pow_two, mul_coeff_three_twoForty68, hc3]
    ring
  have hcsq4 : (c ^ 2).coeff 4 = c.coeff 2 ^ 2 := by
    have h := coeff_mul_at_bounds68 c c 2 2 hc hc
    norm_num at h
    rw [pow_two]
    linear_combination h
  have hcsq5 : (c ^ 2).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hcsqdeg.trans_lt (by norm_num))
  have hBcRaw := mul_coeff_five_twoForty68
    (derivative A * B) (c ^ 2)
  rw [hP1, hP2, hP3, hP4, hP5, hcsq2, hcsq3, hcsq4, hcsq5]
      at hBcRaw
  have hBc : (derivative A * B * c ^ 2).coeff 5 =
      2 * A.coeff 2 * B.coeff 0 * c.coeff 2 ^ 2 +
        6 * A.coeff 3 * B.coeff 0 * c.coeff 1 * c.coeff 2 +
        8 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 2 +
        4 * A.coeff 4 * B.coeff 0 * c.coeff 1 ^ 2 := by
    linear_combination hBcRaw
  have hde := coeff_mul_mul_at_bounds68 (derivative A) d e
    3 0 2 hderA hd he
  norm_num [coeff_derivative] at hde
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 5 := by
    compute_degree; omega
  have hlow4 : (A * B * derivative B * d).natDegree < 5 := by
    compute_degree; omega
  have hlow7 : (B * c * derivative e).natDegree < 5 := by
    compute_degree; omega
  have hlow8 : (B * d * derivative d).natDegree < 5 := by
    compute_degree; omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 5 := by
    compute_degree; omega
  have hlow10 : (c * derivative c * d).natDegree < 5 := by
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
  simp only [coeff_smul, coeff_add, coeff_sub, coeff_neg, hAAF, hBc, hde,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

theorem cubicLoadRowZeroPolynomial68_coeff_five_ordinaryTwoForty68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 =
      (8 / 9 : k) * gamma * A.coeff 4 * B.coeff 0 * c.coeff 2 -
        (2 / 3 : k) * epsilon * A.coeff 4 * A.coeff 2 * B.coeff 0 -
        (1 / 3 : k) * epsilon * A.coeff 3 ^ 2 * B.coeff 0 -
        (4 / 3 : k) * gamma * A.coeff 4 * A.coeff 2 * d.coeff 0 -
        (2 / 3 : k) * gamma * A.coeff 3 ^ 2 * d.coeff 0 := by
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
  have h1 := coeff_mul_mul_at_bounds68 B (derivative A) c
    0 3 2 hB hderA hc
  norm_num [coeff_derivative] at h1
  have hAA5 := mul_derivative_coeff_five_twoForty68 A hA
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hABApoly : A * B * derivative A =
      B.coeff 0 • (A * derivative A) := by
    calc
      A * B * derivative A = A * C (B.coeff 0) * derivative A := by
        exact congrArg (fun q : k[X] => A * q * derivative A) hBC
      _ = B.coeff 0 • (A * derivative A) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have h3 : (A * B * derivative A).coeff 5 =
      B.coeff 0 *
        (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) := by
    rw [hABApoly, coeff_smul, hAA5, smul_eq_mul]
  have hDC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hd
  have hAAdpoly : A * derivative A * d =
      d.coeff 0 • (A * derivative A) := by
    calc
      A * derivative A * d = A * derivative A * C (d.coeff 0) := by
        exact congrArg (fun q : k[X] => A * derivative A * q) hDC
      _ = d.coeff 0 • (A * derivative A) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have h4 : (A * derivative A * d).coeff 5 =
      d.coeff 0 *
        (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) := by
    rw [hAAdpoly, coeff_smul, hAA5, smul_eq_mul]
  have hlow2 : (B * derivative e).natDegree < 5 := by
    compute_degree; omega
  have hlow5 : (d * derivative c).natDegree < 5 := by
    compute_degree; omega
  have hlow6 : (d * derivative A).natDegree < 5 := by
    compute_degree; omega
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 5 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, h1, h3, h4,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6]
  ring

theorem fiveToSix_ordinaryTwoForty_rowZero_five_jet68
    (a a3 a2 b c c1 c0 d y e gamma epsilon i4 : k)
    (ha : a ≠ 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hrigid : 27 * a * i4 + 32 * a * b ^ 3 = 0)
    (hjet : a3 * c - 2 * a * c1 = 0)
    (hconstant : (-8 / 27 : k) * b ^ 3 +
        (8 / 3 : k) * (b * e + c0 * d) +
        2 * epsilon * b + 4 * gamma * d = i4)
    (hrow : (4 / 27 : k) *
          (-(6 * a * a2 + 3 * a3 ^ 2) * (b * e + c0 * d) +
            2 * a2 * b * c ^ 2 + 6 * a3 * b * c1 * c +
            8 * a * b * c0 * c + 4 * a * b * c1 ^ 2 -
            12 * a * d * y) +
        (8 / 9 : k) * gamma * a * b * c -
        (2 / 3 : k) * epsilon * a * a2 * b -
        (1 / 3 : k) * epsilon * a3 ^ 2 * b -
        (4 / 3 : k) * gamma * a * a2 * d -
        (2 / 3 : k) * gamma * a3 ^ 2 * d = 0) :
    2 * a2 * b * c ^ 2 - 4 * a * b * c0 * c -
        2 * a * b * c1 ^ 2 - 3 * a * b * c * gamma +
        6 * a * d * y = 0 := by
  have hwall : 4 * a * (b * e + c0 * d) +
      3 * a * epsilon * b + 6 * a * gamma * d -
        4 * b * c ^ 2 = 0 := by
    linear_combination (1 / 18 : k) * hrigid +
      (3 / 2 : k) * a * hconstant - (4 / 3 : k) * b * hdisc
  have hscaled : (8 : k) * a *
      (2 * a2 * b * c ^ 2 - 4 * a * b * c0 * c -
        2 * a * b * c1 ^ 2 - 3 * a * b * c * gamma +
        6 * a * d * y) = 0 := by
    linear_combination -(27 : k) * a * hrow -
      (6 * a2 * a + 3 * a3 ^ 2) * hwall -
      (12 : k) * a3 * b * c * hjet
  exact (mul_eq_zero.mp hscaled).resolve_left
    (mul_ne_zero (by norm_num) ha)

set_option maxHeartbeats 15000000 in
theorem fiveToSix_offsetTwoForty_nonzero_rowZero_five_source_packet68
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
    (hjet : A.coeff 3 * c.coeff 2 -
      2 * A.coeff 4 * c.coeff 1 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 = 0) :
    (27 * A.coeff 4 * i4 + 32 * A.coeff 4 * B.coeff 0 ^ 3 = 0) ∧
      (A.coeff 3 * c.coeff 2 - 2 * A.coeff 4 * c.coeff 1 = 0) ∧
      (2 * A.coeff 2 * B.coeff 0 * c.coeff 2 ^ 2 -
        4 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 2 -
        2 * A.coeff 4 * B.coeff 0 * c.coeff 1 ^ 2 -
        3 * A.coeff 4 * B.coeff 0 * c.coeff 2 * gamma +
        6 * A.coeff 4 * d.coeff 0 * e.coeff 2 = 0) := by
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
    have hs : (8 / 3 : k) *
        (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0) = 0 := by
      linear_combination hcoeff1
    exact (mul_eq_zero.mp hs).resolve_left (by norm_num)
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
  have hres := secondaryResidualRowZeroPolynomial68_coeff_five_ordinaryTwoForty68
    A B c d e hA hB hc hd he hface hfirst
  have hload := cubicLoadRowZeroPolynomial68_coeff_five_ordinaryTwoForty68
    alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [coeff_add, hres, hload] at hrow
  refine ⟨hrigid, hjet, ?_⟩
  exact fiveToSix_ordinaryTwoForty_rowZero_five_jet68
    (A.coeff 4) (A.coeff 3) (A.coeff 2) (B.coeff 0)
    (c.coeff 2) (c.coeff 1) (c.coeff 0) (d.coeff 0)
    (e.coeff 2) (e.coeff 0) gamma epsilon i4 ha hdisc hrigid hjet
    hconstant (by linear_combination hrow)

#print axioms mul_coeff_five_twoForty68
#print axioms mul_derivative_coeff_five_twoForty68
#print axioms secondaryResidualRowZeroPolynomial68_coeff_five_ordinaryTwoForty68
#print axioms cubicLoadRowZeroPolynomial68_coeff_five_ordinaryTwoForty68
#print axioms fiveToSix_ordinaryTwoForty_rowZero_five_jet68
#print axioms fiveToSix_offsetTwoForty_nonzero_rowZero_five_source_packet68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroFive68

end Max11DegreeRoutes
