import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroRowZeroTwoScratch

/-! # Offset-240 nonzero row-zero coefficient 1 closure

Contracted row-zero coefficient `1` (expanded index `119`) is the terminal
independent row.  After the terminal I3 scalar and all four cusp jets, its
exact value is `(16 / 27) * B₀^3 * c₂`, contradicting the two nonzero edges.
The disjoint pair-zero successor remains available through the import chain.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 25000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem mul_derivative_coeff_one_twoForty68
    (A : k[X]) :
    (A * derivative A).coeff 1 =
      2 * A.coeff 2 * A.coeff 0 + A.coeff 1 ^ 2 := by
  rw [mul_coeff_one]
  norm_num [coeff_derivative]
  ring

theorem secondaryResidualRowZeroPolynomial68_coeff_one_ordinaryTwoForty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0)
    (hfirst : B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 1 =
      (4 / 27 : k) *
        (-(2 * A.coeff 2 * A.coeff 0 + A.coeff 1 ^ 2) *
            (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
          2 * A.coeff 1 * B.coeff 0 * c.coeff 0 * c.coeff 1 +
          2 * A.coeff 2 * B.coeff 0 * c.coeff 0 ^ 2 -
          3 * A.coeff 1 * d.coeff 0 * e.coeff 1 -
          6 * A.coeff 2 * d.coeff 0 * e.coeff 0 +
          6 * B.coeff 0 * c.coeff 0 * e.coeff 2 +
          3 * B.coeff 0 * c.coeff 1 * e.coeff 1 -
          6 * c.coeff 0 * c.coeff 2 * d.coeff 0 -
          3 * c.coeff 1 ^ 2 * d.coeff 0) := by
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
  have hG1 := mul_derivative_coeff_one_twoForty68 A
  have hAAFraw := mul_coeff_one (A * derivative A) F
  rw [hFpos 1 (by norm_num), hG1, hF0] at hAAFraw
  have hAAF : (A * derivative A * F).coeff 1 =
      (2 * A.coeff 2 * A.coeff 0 + A.coeff 1 ^ 2) *
        (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) := by
    linear_combination hAAFraw
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hP0 : (derivative A * B).coeff 0 =
      A.coeff 1 * B.coeff 0 := by
    norm_num [mul_coeff_zero, coeff_derivative]
  have hP1 : (derivative A * B).coeff 1 =
      2 * A.coeff 2 * B.coeff 0 := by
    have h := mul_coeff_one (derivative A) B
    rw [hB1] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hcsq0 : (c ^ 2).coeff 0 = c.coeff 0 ^ 2 := by
    simp only [pow_two, mul_coeff_zero]
  have hcsq1 : (c ^ 2).coeff 1 = 2 * c.coeff 0 * c.coeff 1 := by
    rw [pow_two, mul_coeff_one]
    ring
  have hBcRaw := mul_coeff_one (derivative A * B) (c ^ 2)
  rw [hP0, hP1, hcsq0, hcsq1] at hBcRaw
  have hBc : (derivative A * B * c ^ 2).coeff 1 =
      2 * A.coeff 1 * B.coeff 0 * c.coeff 0 * c.coeff 1 +
        2 * A.coeff 2 * B.coeff 0 * c.coeff 0 ^ 2 := by
    linear_combination hBcRaw
  have hDC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hd
  have hAdePoly : derivative A * d * e =
      d.coeff 0 • (derivative A * e) := by
    calc
      derivative A * d * e = derivative A * C (d.coeff 0) * e := by
        exact congrArg (fun q : k[X] => derivative A * q * e) hDC
      _ = d.coeff 0 • (derivative A * e) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have hAdeRaw := mul_coeff_one (derivative A) e
  norm_num [coeff_derivative] at hAdeRaw
  have hAde : (derivative A * d * e).coeff 1 =
      A.coeff 1 * d.coeff 0 * e.coeff 1 +
        2 * A.coeff 2 * d.coeff 0 * e.coeff 0 := by
    rw [hAdePoly, coeff_smul, smul_eq_mul, hAdeRaw]
    ring
  have hBcePoly : B * c * derivative e =
      B.coeff 0 • (c * derivative e) := by
    calc
      B * c * derivative e = C (B.coeff 0) * c * derivative e := by
        exact congrArg (fun q : k[X] => q * c * derivative e) hBC
      _ = B.coeff 0 • (c * derivative e) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have hceRaw := mul_coeff_one c (derivative e)
  norm_num [coeff_derivative] at hceRaw
  have h7 : (B * c * derivative e).coeff 1 =
      B.coeff 0 *
        (2 * c.coeff 0 * e.coeff 2 + c.coeff 1 * e.coeff 1) := by
    rw [hBcePoly, coeff_smul, smul_eq_mul, hceRaw]
    ring
  have hccdPoly : c * derivative c * d =
      d.coeff 0 • (c * derivative c) := by
    calc
      c * derivative c * d = c * derivative c * C (d.coeff 0) := by
        exact congrArg (fun q : k[X] => c * derivative c * q) hDC
      _ = d.coeff 0 • (c * derivative c) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have hccRaw := mul_coeff_one c (derivative c)
  norm_num [coeff_derivative] at hccRaw
  have h10 : (c * derivative c * d).coeff 1 =
      (2 * c.coeff 0 * c.coeff 2 + c.coeff 1 ^ 2) * d.coeff 0 := by
    rw [hccdPoly, coeff_smul, smul_eq_mul, hccRaw]
    ring
  have hdd : derivative d = 0 := derivative_eq_zero.mpr (Nat.le_zero.mp hd)
  have hdB : derivative B = 0 := derivative_eq_zero.mpr (Nat.le_zero.mp hB)
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 1 := by
    rw [hdd]
    norm_num
  have hlow4 : (A * B * derivative B * d).natDegree < 1 := by
    rw [hdB]
    norm_num
  have hlow8 : (B * d * derivative d).natDegree < 1 := by
    rw [hdd]
    norm_num
  have hlow9 : (derivative B * d ^ 2).natDegree < 1 := by
    rw [hdB]
    norm_num
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
  simp only [coeff_smul, coeff_add, coeff_sub, coeff_neg, hAAF, hBc, hAde,
    h7, h10, coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9, smul_eq_mul]
  ring

theorem cubicLoadRowZeroPolynomial68_coeff_one_ordinaryTwoForty68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 1 =
      (2 / 9 : k) * gamma * B.coeff 0 *
          (A.coeff 1 * c.coeff 1 + 2 * A.coeff 2 * c.coeff 0) +
        (4 / 3 : k) * gamma * B.coeff 0 * e.coeff 2 -
        (1 / 9 : k) * epsilon * B.coeff 0 *
          (2 * A.coeff 2 * A.coeff 0 + A.coeff 1 ^ 2) -
        (2 / 9 : k) * gamma * d.coeff 0 *
          (2 * A.coeff 2 * A.coeff 0 + A.coeff 1 ^ 2) -
        (4 / 3 : k) * gamma * c.coeff 2 * d.coeff 0 -
        (2 / 3 : k) * epsilon * A.coeff 2 * d.coeff 0 := by
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
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hBderAcPoly : B * derivative A * c =
      B.coeff 0 • (derivative A * c) := by
    calc
      B * derivative A * c = C (B.coeff 0) * derivative A * c := by
        exact congrArg (fun q : k[X] => q * derivative A * c) hBC
      _ = B.coeff 0 • (derivative A * c) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have hderAcRaw := mul_coeff_one (derivative A) c
  norm_num [coeff_derivative] at hderAcRaw
  have h1 : (B * derivative A * c).coeff 1 =
      B.coeff 0 *
        (A.coeff 1 * c.coeff 1 + 2 * A.coeff 2 * c.coeff 0) := by
    rw [hBderAcPoly, coeff_smul, smul_eq_mul, hderAcRaw]
    ring
  have hBePoly : B * derivative e =
      B.coeff 0 • derivative e := by
    calc
      B * derivative e = C (B.coeff 0) * derivative e := by
        exact congrArg (fun q : k[X] => q * derivative e) hBC
      _ = B.coeff 0 • derivative e := by
        rw [Polynomial.smul_eq_C_mul]
  have h2 : (B * derivative e).coeff 1 =
      2 * B.coeff 0 * e.coeff 2 := by
    rw [hBePoly, coeff_smul, smul_eq_mul]
    norm_num [coeff_derivative]
    ring
  have hAA1 := mul_derivative_coeff_one_twoForty68 A
  have hABApoly : A * B * derivative A =
      B.coeff 0 • (A * derivative A) := by
    calc
      A * B * derivative A = A * C (B.coeff 0) * derivative A := by
        exact congrArg (fun q : k[X] => A * q * derivative A) hBC
      _ = B.coeff 0 • (A * derivative A) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have h3 : (A * B * derivative A).coeff 1 =
      B.coeff 0 * (2 * A.coeff 2 * A.coeff 0 + A.coeff 1 ^ 2) := by
    rw [hABApoly, coeff_smul, hAA1, smul_eq_mul]
  have hDC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hd
  have hAAdpoly : A * derivative A * d =
      d.coeff 0 • (A * derivative A) := by
    calc
      A * derivative A * d = A * derivative A * C (d.coeff 0) := by
        exact congrArg (fun q : k[X] => A * derivative A * q) hDC
      _ = d.coeff 0 • (A * derivative A) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have h4 : (A * derivative A * d).coeff 1 =
      d.coeff 0 * (2 * A.coeff 2 * A.coeff 0 + A.coeff 1 ^ 2) := by
    rw [hAAdpoly, coeff_smul, hAA1, smul_eq_mul]
  have hdcPoly : d * derivative c =
      d.coeff 0 • derivative c := by
    calc
      d * derivative c = C (d.coeff 0) * derivative c := by
        exact congrArg (fun q : k[X] => q * derivative c) hDC
      _ = d.coeff 0 • derivative c := by
        rw [Polynomial.smul_eq_C_mul]
  have h5 : (d * derivative c).coeff 1 =
      2 * c.coeff 2 * d.coeff 0 := by
    rw [hdcPoly, coeff_smul, smul_eq_mul]
    norm_num [coeff_derivative]
    ring
  have hdAPoly : d * derivative A =
      d.coeff 0 • derivative A := by
    calc
      d * derivative A = C (d.coeff 0) * derivative A := by
        exact congrArg (fun q : k[X] => q * derivative A) hDC
      _ = d.coeff 0 • derivative A := by
        rw [Polynomial.smul_eq_C_mul]
  have h6 : (d * derivative A).coeff 1 =
      2 * A.coeff 2 * d.coeff 0 := by
    rw [hdAPoly, coeff_smul, smul_eq_mul]
    norm_num [coeff_derivative]
    ring
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 1 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul,
    h1, h2, h3, h4, h5, h6]
  ring

theorem fiveToSix_ordinaryTwoForty_rowZero_one_contradiction68
    (a a3 a2 a1 a0 b c c1 c0 d y e1 e0 gamma epsilon : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : d ≠ 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hface : b * y + c * d = 0)
    (hfirst : b * e1 + c1 * d = 0)
    (hjet : a3 * c - 2 * a * c1 = 0)
    (hwall : 4 * a * (b * e0 + c0 * d) +
      3 * a * epsilon * b + 6 * a * gamma * d -
        4 * b * c ^ 2 = 0)
    (hsecond : 2 * a2 * b * c ^ 2 - 4 * a * b * c0 * c -
      2 * a * b * c1 ^ 2 - 3 * a * b * c * gamma +
        6 * a * d * y = 0)
    (hscalar : 4 * b ^ 5 + 9 * b ^ 2 * d * gamma - 18 * d ^ 3 = 0)
    (hthird : a1 * b ^ 4 * d - 2 * b ^ 5 * c1 +
      6 * b ^ 2 * c0 * c1 * d + 18 * c1 * d ^ 3 = 0)
    (hfourth : a0 * b ^ 6 * d - 2 * b ^ 7 * c0 +
      3 * b ^ 4 * c0 ^ 2 * d + 18 * b ^ 2 * c0 * d ^ 3 +
        27 * d ^ 5 = 0)
    (hrow : (4 / 27 : k) *
          (-(2 * a2 * a0 + a1 ^ 2) * (b * e0 + c0 * d) +
            2 * a1 * b * c0 * c1 + 2 * a2 * b * c0 ^ 2 -
            3 * a1 * d * e1 - 6 * a2 * d * e0 +
            6 * b * c0 * y + 3 * b * c1 * e1 -
            6 * c0 * c * d - 3 * c1 ^ 2 * d) +
        (2 / 9 : k) * gamma * b * (a1 * c1 + 2 * a2 * c0) +
        (4 / 3 : k) * gamma * b * y -
        (1 / 9 : k) * epsilon * b * (2 * a2 * a0 + a1 ^ 2) -
        (2 / 9 : k) * gamma * d * (2 * a2 * a0 + a1 ^ 2) -
        (4 / 3 : k) * gamma * c * d -
        (2 / 3 : k) * epsilon * a2 * d = 0) : False := by
  have ha' : a = (-3 * c ^ 2) / b ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hb)).2
    linear_combination hdisc
  have hy' : y = (-c * d) / b := by
    apply (eq_div_iff hb).2
    linear_combination hface
  have he1' : e1 = (-c1 * d) / b := by
    apply (eq_div_iff hb).2
    linear_combination hfirst
  have ha2' : a2 =
      (4 * a * b * c0 * c + 2 * a * b * c1 ^ 2 +
        3 * a * b * c * gamma - 6 * a * d * y) /
          (2 * b * c ^ 2) := by
    apply (eq_div_iff
      (mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero 2 hc))).2
    linear_combination hsecond
  have hepsilon : epsilon =
      (4 * b * c ^ 2 - 4 * a * (b * e0 + c0 * d) -
        6 * a * gamma * d) / (3 * a * b) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb)).2
    linear_combination hwall
  have hgamma : gamma = (18 * d ^ 3 - 4 * b ^ 5) / (9 * b ^ 2 * d) := by
    apply (eq_div_iff
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)) hx)).2
    linear_combination hscalar
  have ha1' : a1 =
      (2 * b ^ 5 * c1 - 6 * b ^ 2 * c0 * c1 * d -
        18 * c1 * d ^ 3) / (b ^ 4 * d) := by
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero 4 hb) hx)).2
    linear_combination hthird
  have ha0' : a0 =
      (2 * b ^ 7 * c0 - 3 * b ^ 4 * c0 ^ 2 * d -
        18 * b ^ 2 * c0 * d ^ 3 - 27 * d ^ 5) / (b ^ 6 * d) := by
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero 6 hb) hx)).2
    linear_combination hfourth
  have hfactor :
      (4 / 27 : k) *
          (-(2 * a2 * a0 + a1 ^ 2) * (b * e0 + c0 * d) +
            2 * a1 * b * c0 * c1 + 2 * a2 * b * c0 ^ 2 -
            3 * a1 * d * e1 - 6 * a2 * d * e0 +
            6 * b * c0 * y + 3 * b * c1 * e1 -
            6 * c0 * c * d - 3 * c1 ^ 2 * d) +
        (2 / 9 : k) * gamma * b * (a1 * c1 + 2 * a2 * c0) +
        (4 / 3 : k) * gamma * b * y -
        (1 / 9 : k) * epsilon * b * (2 * a2 * a0 + a1 ^ 2) -
        (2 / 9 : k) * gamma * d * (2 * a2 * a0 + a1 ^ 2) -
        (4 / 3 : k) * gamma * c * d -
        (2 / 3 : k) * epsilon * a2 * d =
      (16 / 27 : k) * b ^ 3 * c := by
    rw [ha2', hepsilon, hgamma, ha1', ha0', hy', he1', ha']
    field_simp [hb, hc, hx]
    ring
  rw [hfactor] at hrow
  have hnonzero : (16 / 27 : k) * b ^ 3 * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hb)) hc
  exact hnonzero hrow

set_option maxHeartbeats 18000000 in
theorem fiveToSix_offsetTwoForty_nonzero_rowZero_one_source_closure68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0) (hx : d.coeff 0 ≠ 0)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hfirst : B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 = 0)
    (hjet : A.coeff 3 * c.coeff 2 -
      2 * A.coeff 4 * c.coeff 1 = 0)
    (hwall : 4 * A.coeff 4 *
        (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
      3 * A.coeff 4 * epsilon * B.coeff 0 +
      6 * A.coeff 4 * gamma * d.coeff 0 -
        4 * B.coeff 0 * c.coeff 2 ^ 2 = 0)
    (hsecond : 2 * A.coeff 2 * B.coeff 0 * c.coeff 2 ^ 2 -
      4 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 2 -
      2 * A.coeff 4 * B.coeff 0 * c.coeff 1 ^ 2 -
      3 * A.coeff 4 * B.coeff 0 * c.coeff 2 * gamma +
        6 * A.coeff 4 * d.coeff 0 * e.coeff 2 = 0)
    (hscalar : 4 * B.coeff 0 ^ 5 +
      9 * B.coeff 0 ^ 2 * d.coeff 0 * gamma -
        18 * d.coeff 0 ^ 3 = 0)
    (hthird : A.coeff 1 * B.coeff 0 ^ 4 * d.coeff 0 -
      2 * B.coeff 0 ^ 5 * c.coeff 1 +
      6 * B.coeff 0 ^ 2 * c.coeff 0 * c.coeff 1 * d.coeff 0 +
        18 * c.coeff 1 * d.coeff 0 ^ 3 = 0)
    (hfourth : A.coeff 0 * B.coeff 0 ^ 6 * d.coeff 0 -
      2 * B.coeff 0 ^ 7 * c.coeff 0 +
      3 * B.coeff 0 ^ 4 * c.coeff 0 ^ 2 * d.coeff 0 +
      18 * B.coeff 0 ^ 2 * c.coeff 0 * d.coeff 0 ^ 3 +
        27 * d.coeff 0 ^ 5 = 0)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 1 = 0) : False := by
  rw [coeff_add,
    secondaryResidualRowZeroPolynomial68_coeff_one_ordinaryTwoForty68
      A B c d e hA hB hc hd he hface hfirst,
    cubicLoadRowZeroPolynomial68_coeff_one_ordinaryTwoForty68
      alpha gamma epsilon eta A B c d e hA hB hc hd he] at hrow
  exact fiveToSix_ordinaryTwoForty_rowZero_one_contradiction68
    (A.coeff 4) (A.coeff 3) (A.coeff 2) (A.coeff 1) (A.coeff 0)
    (B.coeff 0) (c.coeff 2) (c.coeff 1) (c.coeff 0)
    (d.coeff 0) (e.coeff 2) (e.coeff 1) (e.coeff 0)
    gamma epsilon ha hb hcTop hx hdisc hface hfirst hjet hwall
    hsecond hscalar hthird hfourth (by linear_combination hrow)

#print axioms mul_derivative_coeff_one_twoForty68
#print axioms secondaryResidualRowZeroPolynomial68_coeff_one_ordinaryTwoForty68
#print axioms cubicLoadRowZeroPolynomial68_coeff_one_ordinaryTwoForty68
#print axioms fiveToSix_ordinaryTwoForty_rowZero_one_contradiction68
#print axioms fiveToSix_offsetTwoForty_nonzero_rowZero_one_source_closure68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroOne68

end Max11DegreeRoutes
