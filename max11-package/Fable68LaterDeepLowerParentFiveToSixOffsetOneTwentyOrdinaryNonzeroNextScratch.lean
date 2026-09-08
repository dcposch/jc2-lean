import Fable68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryNonzeroScratch

/-! # Continuing the preserved ordinary nonzero-discriminant packet

After the offset-`120` all-nonzero elimination, the ordinary
nonzero-discriminant alternative of the `(n,g)=(120,360)` wall survives
only on the offset-`180` face retained by the pair-zero successor, in the
contracted `(4,0,2,1,3)` chart.  In its row-zero tower the coefficients
`10,9,8` (expanded `659,599,539`) only regenerate the face and the two
lower I4 jets — at coefficient `8` the row load `(-8/9)*gamma*a^2*d₁`
cancels against the I4 coefficient-`1` jet exactly as at offset `120` —
and coefficient `7` (expanded `479`) is already consumed by the existing
offset-`180` row-zero packet.  The next unused row-zero coefficient is
therefore `6` (expanded `419`).  It is consumed here together with the
load-free I3 coefficient `4` (expanded `240`), which was so far used only
as a degree truncation and is expanded in coordinates for the first time.
Every `epsilon` and `gamma` load cancels exactly through the retained I4
coefficient-`1` and constant jets and the rigid I4 residual, and the
branch gains two fresh relations: the discriminant first jet
`a₃*b^2 + 6*c₁*c₂ = 0` and the edge alignment `2*c₂*d₀ = c₁*d₁`, hence
also `2*b*e₂ + 3*c₁*d₁ = 0`.  No branch is closed and no stored nonzero
is divided away; the pair-zero offset-`180` sibling, the row-one tower,
the offset-`120` small chart, and the aligned second-jet lane are
untouched. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryNonzeroNext68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The coefficient of order four in a product. -/
theorem mul_coeff_four_oneTwentyOrdinaryNonzeroNext68 (p q : k[X]) :
    (p * q).coeff 4 =
      p.coeff 0 * q.coeff 4 + p.coeff 1 * q.coeff 3 +
        p.coeff 2 * q.coeff 2 + p.coeff 3 * q.coeff 1 +
        p.coeff 4 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- The coefficient of order five in a product. -/
theorem mul_coeff_five_oneTwentyOrdinaryNonzeroNext68 (p q : k[X]) :
    (p * q).coeff 5 =
      p.coeff 0 * q.coeff 5 + p.coeff 1 * q.coeff 4 +
        p.coeff 2 * q.coeff 3 + p.coeff 3 * q.coeff 2 +
        p.coeff 4 * q.coeff 1 + p.coeff 5 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- The coefficient of order six in a product. -/
theorem mul_coeff_six_oneTwentyOrdinaryNonzeroNext68 (p q : k[X]) :
    (p * q).coeff 6 =
      p.coeff 0 * q.coeff 6 + p.coeff 1 * q.coeff 5 +
        p.coeff 2 * q.coeff 4 + p.coeff 3 * q.coeff 3 +
        p.coeff 4 * q.coeff 2 + p.coeff 5 * q.coeff 1 +
        p.coeff 6 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- Second-from-top coefficient of `A * A'` in the quartic chart. -/
theorem mul_derivative_coeff_six_oneTwentyOrdinaryNonzeroNext68
    (A : k[X]) (hA : A.natDegree ≤ 4) :
    (A * derivative A).coeff 6 = 7 * A.coeff 4 * A.coeff 3 := by
  have hA5 : A.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have hA6 : A.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have hA7 : A.coeff 7 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have h := mul_coeff_six_oneTwentyOrdinaryNonzeroNext68 A (derivative A)
  norm_num [coeff_derivative, hA5, hA6, hA7] at h
  linear_combination h

/-- Third-from-top coefficient of `A * A'` in the quartic chart. -/
theorem mul_derivative_coeff_five_oneTwentyOrdinaryNonzeroNext68
    (A : k[X]) (hA : A.natDegree ≤ 4) :
    (A * derivative A).coeff 5 =
      6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2 := by
  have hA5 : A.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have hA6 : A.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have h := mul_coeff_five_oneTwentyOrdinaryNonzeroNext68 A (derivative A)
  norm_num [coeff_derivative, hA5, hA6] at h
  linear_combination h

/-- The load-free I3 coefficient `4` (expanded `240`) in coordinates.  In
the existing row-one packet it was only used as a degree truncation; here
its literal content is extracted. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_four_ordinaryNonzeroNextOneEighty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff 4 =
      (8 / 9 : k) *
        (-(A.coeff 4 * B.coeff 0 * d.coeff 0) -
          A.coeff 3 * B.coeff 0 * d.coeff 1 +
          3 * c.coeff 2 * e.coeff 2 + 3 * c.coeff 1 * e.coeff 3) := by
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd4 : d.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hc4 : c.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have he4 : e.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB3 : B.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB4 : B.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hAB3 : (A * B).coeff 3 = A.coeff 3 * B.coeff 0 := by
    rw [mul_coeff_three_oneTwentyOrdinaryNonzero68, hB1, hB2, hB3]
    ring
  have hAB4 := coeff_mul_at_bounds68 A B 4 0 hA hB
  norm_num at hAB4
  have hABd4 : (A * B * d).coeff 4 =
      A.coeff 3 * B.coeff 0 * d.coeff 1 +
        A.coeff 4 * B.coeff 0 * d.coeff 0 := by
    have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68 (A * B) d
    rw [hd2, hd3, hd4, hAB3, hAB4] at h
    linear_combination h
  have hce4 : (c * e).coeff 4 =
      c.coeff 1 * e.coeff 3 + c.coeff 2 * e.coeff 2 := by
    have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68 c e
    rw [hc3, hc4, he4] at h
    linear_combination h
  have hB2c : (B ^ 2 * c).natDegree < 4 := by
    compute_degree
    omega
  have hdsq : (d ^ 2).natDegree < 4 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd4, hce4,
    coeff_eq_zero_of_natDegree_lt hB2c,
    coeff_eq_zero_of_natDegree_lt hdsq]
  ring

/-- Homogeneous row-zero coefficient `6` (expanded `419`).  The two
already-consumed I4 jets kill the high coefficients of `B*e+c*d`; the
surviving terms carry the second `A`-jet against the tied low jets, the
first `c`-jet against the discriminant core, and the loaded edge
products. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_six_ordinaryNonzeroNextOneEighty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hsecond : B.coeff 0 * e.coeff 2 +
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 6 =
      (4 / 27 : k) *
        (-((6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) *
            (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
              c.coeff 0 * d.coeff 1)) -
          7 * A.coeff 4 * A.coeff 3 *
            (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
          3 * A.coeff 3 * B.coeff 0 * c.coeff 2 ^ 2 +
          8 * A.coeff 4 * B.coeff 0 * c.coeff 1 * c.coeff 2 -
          9 * A.coeff 3 * d.coeff 1 * e.coeff 3 -
          12 * A.coeff 4 * (d.coeff 0 * e.coeff 3 + d.coeff 1 * e.coeff 2)) := by
  let F : k[X] := B * e + c * d
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hF : F.natDegree ≤ 3 := by simp only [F]; compute_degree; omega
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB3 : B.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have he4 : e.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have he5 : e.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have he6 : e.coeff 6 = 0 :=
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
  have hF0 : F.coeff 0 =
      B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0 := by
    simp only [F, coeff_add, mul_coeff_zero]
  have hF1 : F.coeff 1 =
      B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
        c.coeff 0 * d.coeff 1 := by
    simp only [F, coeff_add, mul_coeff_one]
    rw [hB1]
    ring
  have hF4 : F.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hF.trans_lt (by norm_num))
  have hF5 : F.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hF.trans_lt (by norm_num))
  have hF6 : F.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hF.trans_lt (by norm_num))
  have hG5 := mul_derivative_coeff_five_oneTwentyOrdinaryNonzeroNext68 A hA
  have hG6 := mul_derivative_coeff_six_oneTwentyOrdinaryNonzeroNext68 A hA
  have hAAF : (A * derivative A * F).coeff 6 =
      (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) *
          (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
            c.coeff 0 * d.coeff 1) +
        7 * A.coeff 4 * A.coeff 3 *
          (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) := by
    have h := mul_coeff_six_oneTwentyOrdinaryNonzeroNext68
      (A * derivative A) F
    rw [hF2, hF3, hF4, hF5, hF6, hG5, hG6, hF0, hF1] at h
    linear_combination h
  have hA'Bdeg : (derivative A * B).natDegree ≤ 3 := by
    compute_degree
    omega
  have hA'B4 : (derivative A * B).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
  have hA'B5 : (derivative A * B).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
  have hA'B6 : (derivative A * B).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
  have hA'B2 : (derivative A * B).coeff 2 =
      3 * A.coeff 3 * B.coeff 0 := by
    have h := mul_coeff_two68 (derivative A) B
    rw [hB1, hB2] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hA'B3 : (derivative A * B).coeff 3 =
      4 * A.coeff 4 * B.coeff 0 := by
    have h := mul_coeff_three_oneTwentyOrdinaryNonzero68 (derivative A) B
    rw [hB1, hB2, hB3] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hcsqdeg : (c ^ 2).natDegree ≤ 4 := by
    compute_degree
    omega
  have hcsq5 : (c ^ 2).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hcsqdeg.trans_lt (by norm_num))
  have hcsq6 : (c ^ 2).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hcsqdeg.trans_lt (by norm_num))
  have hcsq4 : (c ^ 2).coeff 4 = c.coeff 2 ^ 2 := by
    have h := coeff_mul_at_bounds68 c c 2 2 hc hc
    norm_num at h
    rw [pow_two]
    linear_combination h
  have hcsq3 : (c ^ 2).coeff 3 = 2 * c.coeff 1 * c.coeff 2 := by
    rw [pow_two, mul_coeff_three_oneTwentyOrdinaryNonzero68, hc3]
    ring
  have hBc2 : (derivative A * B * c ^ 2).coeff 6 =
      3 * A.coeff 3 * B.coeff 0 * c.coeff 2 ^ 2 +
        8 * A.coeff 4 * B.coeff 0 * c.coeff 1 * c.coeff 2 := by
    have h := mul_coeff_six_oneTwentyOrdinaryNonzeroNext68
      (derivative A * B) (c ^ 2)
    rw [hcsq5, hcsq6, hA'B4, hA'B5, hA'B6, hA'B2, hA'B3,
      hcsq3, hcsq4] at h
    linear_combination h
  have hA'dDeg : (derivative A * d).natDegree ≤ 4 := by
    compute_degree
    omega
  have hA'd5 : (derivative A * d).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'dDeg.trans_lt (by norm_num))
  have hA'd6 : (derivative A * d).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'dDeg.trans_lt (by norm_num))
  have hA'd4 : (derivative A * d).coeff 4 =
      4 * A.coeff 4 * d.coeff 1 := by
    have h := coeff_mul_at_bounds68 (derivative A) d 3 1 hderA hd
    norm_num [coeff_derivative] at h
    linear_combination h
  have hA'd3 : (derivative A * d).coeff 3 =
      3 * A.coeff 3 * d.coeff 1 + 4 * A.coeff 4 * d.coeff 0 := by
    have h := mul_coeff_three_oneTwentyOrdinaryNonzero68 (derivative A) d
    rw [hd2, hd3] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hde : (derivative A * d * e).coeff 6 =
      3 * A.coeff 3 * d.coeff 1 * e.coeff 3 +
        4 * A.coeff 4 * d.coeff 0 * e.coeff 3 +
        4 * A.coeff 4 * d.coeff 1 * e.coeff 2 := by
    have h := mul_coeff_six_oneTwentyOrdinaryNonzeroNext68
      (derivative A * d) e
    rw [he4, he5, he6, hA'd5, hA'd6, hA'd3, hA'd4] at h
    linear_combination h
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 6 := by
    compute_degree
    omega
  have hlow4 : (A * B * derivative B * d).natDegree < 6 := by
    compute_degree
    omega
  have hlow7 : (B * c * derivative e).natDegree < 6 := by
    compute_degree
    omega
  have hlow8 : (B * d * derivative d).natDegree < 6 := by
    compute_degree
    omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 6 := by
    compute_degree
    omega
  have hlow10 : (c * derivative c * d).natDegree < 6 := by
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
  simp only [coeff_smul, coeff_add, coeff_sub, coeff_neg, hAAF, hBc2, hde,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

/-- Exact literal load at the same coefficient: the `epsilon` load sits on
the second `A`-jet against `b`, the `gamma` load on the second `A`-jet
against the retained `d`-edge. -/
theorem cubicLoadRowZeroPolynomial68_coeff_six_ordinaryNonzeroNextOneEighty68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 =
      (-7 / 9 : k) * epsilon * A.coeff 4 * A.coeff 3 * B.coeff 0 -
        (4 / 3 : k) * gamma * A.coeff 4 * A.coeff 2 * d.coeff 1 -
        (2 / 3 : k) * gamma * A.coeff 3 ^ 2 * d.coeff 1 -
        (14 / 9 : k) * gamma * A.coeff 4 * A.coeff 3 * d.coeff 0 := by
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
  have hdA4 : (derivative A).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hderA.trans_lt (by norm_num))
  have hdA5 : (derivative A).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hderA.trans_lt (by norm_num))
  have hdA6 : (derivative A).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hderA.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB3 : B.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd4 : d.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd5 : d.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd6 : d.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hABdeg : (A * B).natDegree ≤ 4 := by
    compute_degree
    omega
  have hAB5 : (A * B).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hABdeg.trans_lt (by norm_num))
  have hAB6 : (A * B).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hABdeg.trans_lt (by norm_num))
  have hAB3 : (A * B).coeff 3 = A.coeff 3 * B.coeff 0 := by
    rw [mul_coeff_three_oneTwentyOrdinaryNonzero68, hB1, hB2, hB3]
    ring
  have hAB4 := coeff_mul_at_bounds68 A B 4 0 hA hB
  norm_num at hAB4
  have hABA' : (A * B * derivative A).coeff 6 =
      7 * A.coeff 4 * A.coeff 3 * B.coeff 0 := by
    have h := mul_coeff_six_oneTwentyOrdinaryNonzeroNext68
      (A * B) (derivative A)
    rw [hdA4, hdA5, hdA6, hAB5, hAB6, hAB3, hAB4] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hG5 := mul_derivative_coeff_five_oneTwentyOrdinaryNonzeroNext68 A hA
  have hG6 := mul_derivative_coeff_six_oneTwentyOrdinaryNonzeroNext68 A hA
  have hAAd : (A * derivative A * d).coeff 6 =
      (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) * d.coeff 1 +
        7 * A.coeff 4 * A.coeff 3 * d.coeff 0 := by
    have h := mul_coeff_six_oneTwentyOrdinaryNonzeroNext68
      (A * derivative A) d
    rw [hd2, hd3, hd4, hd5, hd6, hG5, hG6] at h
    linear_combination h
  have hlow1 : (B * derivative A * c).natDegree < 6 := by
    compute_degree
    omega
  have hlow2 : (B * derivative e).natDegree < 6 := by
    compute_degree
    omega
  have hlow5 : (d * derivative c).natDegree < 6 := by
    compute_degree
    omega
  have hlow6 : (d * derivative A).natDegree < 6 := by
    compute_degree
    omega
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 6 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, hABA', hAAd,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6]
  ring

/-- Scalar residual of the loaded row-zero coefficient `6` against the
retained jets: the `gamma` loads cancel through the I4 coefficient-`1`
jet, the `epsilon` and remaining `gamma` loads through the I4 constant
jet, and the `i4` value through the rigid residual.  The row then forces
the discriminant first jet and the edge alignment; no stored nonzero is
divided away. -/
theorem fiveToSix_ordinaryNonzeroNext_rowSix_residual68
    (a a₂ a₃ b c₀ c₁ c₂ d₀ d₁ e₀ e₁ e₂ e₃ gamma epsilon i4 : k)
    (ha : a ≠ 0) (hcTop : c₂ ≠ 0) (hx : d₁ ≠ 0)
    (hface : b * e₃ + c₂ * d₁ = 0)
    (hdisc : a * b ^ 2 + 3 * c₂ ^ 2 = 0)
    (hsecond : b * e₂ + c₂ * d₀ + c₁ * d₁ = 0)
    (hfirst : (8 / 3 : k) * (b * e₁ + c₁ * d₀ + c₀ * d₁) +
      4 * gamma * d₁ = 0)
    (hconstant : (-8 / 27 : k) * b ^ 3 +
      (8 / 3 : k) * (b * e₀ + c₀ * d₀) +
      2 * epsilon * b + 4 * gamma * d₀ = i4)
    (hrigid : 27 * a * i4 + 32 * a * b ^ 3 + 216 * d₁ * e₃ = 0)
    (hfour : -(a * b * d₀) - a₃ * b * d₁ +
      3 * c₂ * e₂ + 3 * c₁ * e₃ = 0)
    (hrow : (4 / 27 : k) *
        (-((6 * a * a₂ + 3 * a₃ ^ 2) *
            (b * e₁ + c₁ * d₀ + c₀ * d₁)) -
          7 * a * a₃ * (b * e₀ + c₀ * d₀) +
          3 * a₃ * b * c₂ ^ 2 + 8 * a * b * c₁ * c₂ -
          9 * a₃ * d₁ * e₃ -
          12 * a * (d₀ * e₃ + d₁ * e₂)) +
        ((-7 / 9 : k) * epsilon * a * a₃ * b -
          (4 / 3 : k) * gamma * a * a₂ * d₁ -
          (2 / 3 : k) * gamma * a₃ ^ 2 * d₁ -
          (14 / 9 : k) * gamma * a * a₃ * d₀) = 0) :
    a₃ * b ^ 2 + 6 * c₁ * c₂ = 0 ∧
      2 * c₂ * d₀ - c₁ * d₁ = 0 ∧
      2 * b * e₂ + 3 * c₁ * d₁ = 0 := by
  have hT1s : d₁ * (a₃ * b ^ 2 + 6 * c₁ * c₂) = 0 := by
    linear_combination (-b) * hfour + 3 * c₂ * hsecond +
      3 * c₁ * hface - d₀ * hdisc
  have hT1 : a₃ * b ^ 2 + 6 * c₁ * c₂ = 0 :=
    (mul_eq_zero.mp hT1s).resolve_left hx
  have hE : -(a₃ * b * c₂ ^ 2) + 3 * a₃ * d₁ * e₃ +
      2 * a * b * c₁ * c₂ - 3 * a * d₀ * e₃ - 3 * a * d₁ * e₂ = 0 := by
    linear_combination (27 / 16 : k) * hrow +
      ((9 / 16 : k) * a * a₂ + (9 / 32 : k) * a₃ ^ 2) * hfirst +
      (21 / 32 : k) * a * a₃ * hconstant +
      (7 / 288 : k) * a₃ * hrigid -
      (7 / 12 : k) * a₃ * b * hdisc
  have hT2s : a * (c₂ * (d₁ * (2 * c₂ * d₀ - c₁ * d₁))) = 0 := by
    linear_combination (1 / 3 : k) * b * c₂ * hE +
      (1 / 3 : k) * a * b * d₁ * hfour -
      (a * c₁ * d₁ - a * c₂ * d₀ + a₃ * c₂ * d₁) * hface +
      (1 / 3 : k) * c₂ ^ 3 * hT1 +
      (1 / 3 : k) * (a * d₀ * d₁ + a₃ * d₁ ^ 2 - 2 * c₁ * c₂ ^ 2) * hdisc
  have hT2 : 2 * c₂ * d₀ - c₁ * d₁ = 0 := by
    have h1 := (mul_eq_zero.mp hT2s).resolve_left ha
    have h2 := (mul_eq_zero.mp h1).resolve_left hcTop
    exact (mul_eq_zero.mp h2).resolve_left hx
  have hT3 : 2 * b * e₂ + 3 * c₁ * d₁ = 0 := by
    linear_combination 2 * hsecond - hT2
  exact ⟨hT1, hT2, hT3⟩

set_option maxHeartbeats 15000000 in
/-- Source-facing continuation of the preserved ordinary offset-`120`
nonzero-discriminant packet on its offset-`180` face.  Row-zero
coefficient `6` (expanded `419`) is the next unused row: coefficients
`659`, `599` only regenerate the face and the I4 coefficient-`2` jet,
coefficient `539` only regenerates the loaded I4 coefficient-`1` jet, and
coefficient `479` is consumed by the existing row-zero packet whose rigid
I4 residual is retained here as a literal hypothesis.  Together with the
load-free I3 coefficient `4` (expanded `240`) the row forces the
discriminant first jet and the edge alignment.  The pair-zero
offset-`180` sibling, the row-one tower, and the aligned second-jet lane
are preserved literally elsewhere. -/
theorem fiveToSix_offsetOneEighty_ordinaryNonzeroNext_source_packet68
    (alpha gamma epsilon eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 1 ≠ 0) (hy : e.coeff 3 ≠ 0)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hi4rigid : 27 * A.coeff 4 * i4 + 32 * A.coeff 4 * B.coeff 0 ^ 3 +
      216 * d.coeff 1 * e.coeff 3 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 = 0) :
    A.coeff 3 * B.coeff 0 ^ 2 + 6 * c.coeff 1 * c.coeff 2 = 0 ∧
      2 * c.coeff 2 * d.coeff 0 - c.coeff 1 * d.coeff 1 = 0 ∧
      2 * B.coeff 0 * e.coeff 2 + 3 * c.coeff 1 * d.coeff 1 = 0 := by
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
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
    coeff_smul, smul_eq_mul, mul_coeff_one, hB1, hBcube1, coeff_C]
    at hcoeff1
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
  have hc4 : c.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have he4 : e.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hB2deg : (B ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hB24 : (B ^ 2).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2deg.trans_lt (by norm_num))
  have hI3J : secondaryResidualInvariantThreePolynomial68 A B c d e +
      (2 * epsilon : k) • c + (4 * gamma : k) • e -
      (2 / 3 * gamma : k) • B ^ 2 = C i3 := by
    have hres := hi3
    rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
      at hres
    simp only [zero_smul, zero_add] at hres
    simpa only [add_zero] using hres
  have h4 := congrArg (fun p : k[X] => p.coeff 4) hI3J
  norm_num [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_C,
    hc4, he4, hB24] at h4
  have hJ4c :=
    secondaryResidualInvariantThreePolynomial68_coeff_four_ordinaryNonzeroNextOneEighty68
      A B c d e hA hB hc hd he
  have hfour : -(A.coeff 4 * B.coeff 0 * d.coeff 0) -
      A.coeff 3 * B.coeff 0 * d.coeff 1 +
      3 * c.coeff 2 * e.coeff 2 + 3 * c.coeff 1 * e.coeff 3 = 0 := by
    linear_combination (9 / 8 : k) * h4 - (9 / 8 : k) * hJ4c
  have hres6 :=
    secondaryResidualRowZeroPolynomial68_coeff_six_ordinaryNonzeroNextOneEighty68
      A B c d e hA hB hc hd he hface hsecond
  have hload6 :=
    cubicLoadRowZeroPolynomial68_coeff_six_ordinaryNonzeroNextOneEighty68
      alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [coeff_add, hres6, hload6] at hrow
  exact fiveToSix_ordinaryNonzeroNext_rowSix_residual68
    (A.coeff 4) (A.coeff 2) (A.coeff 3) (B.coeff 0)
    (c.coeff 0) (c.coeff 1) (c.coeff 2) (d.coeff 0) (d.coeff 1)
    (e.coeff 0) (e.coeff 1) (e.coeff 2) (e.coeff 3) gamma epsilon i4
    ha hcTop hx hface hdisc hsecond hfirst hconstant hi4rigid
    (by linear_combination hfour) (by linear_combination hrow)

#print axioms mul_coeff_four_oneTwentyOrdinaryNonzeroNext68
#print axioms mul_coeff_five_oneTwentyOrdinaryNonzeroNext68
#print axioms mul_coeff_six_oneTwentyOrdinaryNonzeroNext68
#print axioms mul_derivative_coeff_six_oneTwentyOrdinaryNonzeroNext68
#print axioms mul_derivative_coeff_five_oneTwentyOrdinaryNonzeroNext68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_four_ordinaryNonzeroNextOneEighty68
#print axioms secondaryResidualRowZeroPolynomial68_coeff_six_ordinaryNonzeroNextOneEighty68
#print axioms cubicLoadRowZeroPolynomial68_coeff_six_ordinaryNonzeroNextOneEighty68
#print axioms fiveToSix_ordinaryNonzeroNext_rowSix_residual68
#print axioms fiveToSix_offsetOneEighty_ordinaryNonzeroNext_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryNonzeroNext68

end Max11DegreeRoutes
